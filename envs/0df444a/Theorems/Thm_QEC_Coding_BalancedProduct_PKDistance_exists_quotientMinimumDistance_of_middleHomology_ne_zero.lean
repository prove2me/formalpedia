-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_exists_quotientMinimumDistance_of_middleHomology_ne_zero
-- name    : QEC.Coding.BalancedProduct.PKDistance.exists_quotientMinimumDistance_of_middleHomology_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:06:17.346274+00:00
-- url     : https://prove2.me/theorems/a1153d79-e507-4940-9955-2d84a7591173
-- title:
--   PKDistance: exists quotient Minimum Distance of middle Homology ne zero
-- statement:
--   A nonzero quotient Tanner homology class supplies a nonzero quotient
--   cycle, hence an attained finite minimum distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L3087-L3109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L3087-L3109

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w

theorem QEC.Coding.BalancedProduct.PKDistance.exists_quotientMinimumDistance_of_middleHomology_ne_zero
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G))
    (hClass : (HorizontalSubsystem.quotientTannerComplex A).middleHomology)
    (hClassNe : hClass ≠ 0) :
    ∃ d : Nat, MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex A).middleCycleCode d := by sorry
