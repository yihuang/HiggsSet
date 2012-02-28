{-# LANGUAGE TemplateHaskell #-}
module Data.HiggsSet.TH (deriveIndexInstances) where

import Safe (lastDef)
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

deriveIndexInstances :: Name -> Q [Dec]
deriveIndexInstances idxTy =
    withType idxTy $ \tvbs cons -> do
        enum <- enumInstance tvbs cons
        bounded <- boundedInstance tvbs cons
        return [enum, bounded]
  where
    undefinedCon :: Con -> ExpQ
    undefinedCon con = foldl appE (conE $ getConName con) $
                           zipWith (curry fst) (repeat [|undefined|]) (getConArgs con)
    conWildP :: Con -> PatQ
    conWildP con = conP (getConName con) $
                       zipWith (curry fst) (repeat wildP) (getConArgs con)
    instanceType :: [TyVarBndr] -> TypeQ
    instanceType tvbs = foldl appT (conT idxTy) $ map (varT . tvbName) tvbs

    enumInstance :: [TyVarBndr] -> [Con] -> Q Dec
    enumInstance tvbs cons =
        instanceD (return [])
                  (conT ''Enum `appT` instanceType tvbs)
                  [ funD 'fromEnum
                      [ clause [conWildP con]
                               (normalB $ litE $ IntegerL n)
                               []
                      | (n, con) <- zip [0..] cons
                      ]
                  , funD 'toEnum $
                      [ clause [litP $ IntegerL n]
                               (normalB $ undefinedCon con)
                               []
                      | (n, con) <- zip [0..] cons
                      ] ++
                      [ clause [wildP]
                               (normalB $ [|error|] `appE` litE (stringL "out of bound [toEnum]"))
                               []
                      ]
                  ]

    boundedInstance :: [TyVarBndr] -> [Con] -> Q Dec
    boundedInstance tvbs (firstCon:rest) =
        instanceD (return [])
                  (conT ''Bounded `appT` instanceType tvbs)
                  [ funD 'minBound
                      [ clause []
                               (normalB $ undefinedCon firstCon)
                               []
                      ]
                  , funD 'maxBound
                      [ clause []
                               (normalB $ undefinedCon (lastDef firstCon rest))
                               []
                      ]
                  ]
    boundedInstance _ [] = error "FundServer.TH.deriveIndexInstances: \
                                 \Not a single constructor given!"

-- copied from aeson
--------------------------------------------------------------------------------
-- Utility functions
--------------------------------------------------------------------------------

-- | Boilerplate for top level splices.
--
-- The given 'Name' must be from a type constructor. Furthermore, the
-- type constructor must be either a data type or a newtype. Any other
-- value will result in an exception.
withType :: Name
         -> ([TyVarBndr] -> [Con] -> Q a)
         -- ^ Function that generates the actual code. Will be applied
         -- to the type variable binders and constructors extracted
         -- from the given 'Name'.
         -> Q a
         -- ^ Resulting value in the 'Q'uasi monad.
withType name f = do
    info <- reify name
    case info of
      TyConI dec ->
        case dec of
          DataD    _ _ tvbs cons _ -> f tvbs cons
          NewtypeD _ _ tvbs con  _ -> f tvbs [con]
          other -> error $ "FundServer.TH.withType: Unsupported type: "
                          ++ show other
      _ -> error "FundServer.TH.withType: I need the name of a type."

-- | Extracts the name from a constructor.
getConName :: Con -> Name
getConName (NormalC name _)  = name
getConName (RecC name _)     = name
getConName (InfixC _ name _) = name
getConName (ForallC _ _ con) = getConName con

-- | Extracts the args from a constructor
getConArgs :: Con -> [StrictType]
getConArgs (NormalC _ st)  = st
getConArgs (RecC _ vst)     = [(s, t) | (_, s, t) <- vst]
getConArgs (InfixC t1 _ t2) = [t1, t2]          
getConArgs (ForallC _ _ con) = getConArgs con

-- | Extracts the name from a type variable binder.
tvbName :: TyVarBndr -> Name
tvbName (PlainTV  name  ) = name
tvbName (KindedTV name _) = name
