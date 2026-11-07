-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_binaryOverlap_cyclicShift_eq_sum
-- name    : QEC.Coding.BalancedProduct.PKDistance.binaryOverlap_cyclicShift_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:01:59.402367+00:00
-- url     : https://prove2.me/theorems/e40d554f-864b-4ac1-952b-e254672ec587
-- title:
--   PKDistance: binary Overlap cyclic Shift eq sum
-- statement:
--   Overlap with a cyclic shift decomposes fibrewise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L152-L166
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L152-L166

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

theorem QEC.Coding.BalancedProduct.PKDistance.binaryOverlap_cyclicShift_eq_sum
    {I : Type u} {G : Type v} [Group G]
    [Fintype I] [Fintype G] (t : G)
    (z : Word (ZMod 2) (I × G)) :
    binaryOverlap z (cyclicShift t z) =
      ∑ i, ∑ g, if z (i, g) ≠ 0 ∧ z (i, g * t⁻¹) ≠ 0 then 1 else 0 := by sorry
