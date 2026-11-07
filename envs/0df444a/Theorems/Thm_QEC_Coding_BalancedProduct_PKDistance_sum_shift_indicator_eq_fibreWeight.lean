-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_sum_shift_indicator_eq_fibreWeight
-- name    : QEC.Coding.BalancedProduct.PKDistance.sum_shift_indicator_eq_fibreWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:01:58.018277+00:00
-- url     : https://prove2.me/theorems/08de15d3-3104-4284-bab8-153069fbae4a
-- title:
--   PKDistance: sum shift indicator eq fibre Weight
-- statement:
--   For a fixed cyclic coordinate, summing the second support indicator over
--   all translations recovers the weight of that fibre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L170-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L170-L179

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

theorem QEC.Coding.BalancedProduct.PKDistance.sum_shift_indicator_eq_fibreWeight
    {I : Type u} {G : Type v} [Group G]
    [Fintype G] (z : Word (ZMod 2) (I × G)) (i : I) (g : G) :
    (∑ t, if z (i, g * t⁻¹) ≠ 0 then 1 else 0) = fibreWeight z i := by sorry
