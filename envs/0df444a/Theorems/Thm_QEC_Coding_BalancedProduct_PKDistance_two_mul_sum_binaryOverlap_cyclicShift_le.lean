-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_two_mul_sum_binaryOverlap_cyclicShift_le
-- name    : QEC.Coding.BalancedProduct.PKDistance.two_mul_sum_binaryOverlap_cyclicShift_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:02:10.530544+00:00
-- url     : https://prove2.me/theorems/ce45c0b6-72a0-468e-a2f3-1ca8f75f3904
-- title:
--   PKDistance: two mul sum binary Overlap cyclic Shift le
-- statement:
--   The fibrewise half-circle condition bounds twice the total cyclic
--   autocorrelation by `|G|` times the total weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L222-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L222-L238

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

theorem QEC.Coding.BalancedProduct.PKDistance.two_mul_sum_binaryOverlap_cyclicShift_le
    {I : Type u} {G : Type v} [Group G]
    [Fintype I] [Fintype G]
    (z : Word (ZMod 2) (I × G))
    (hhalf : ∀ i, 2 * fibreWeight z i ≤ Fintype.card G) :
    2 * (∑ t, binaryOverlap z (cyclicShift t z)) ≤
      Fintype.card G * HammingWeight z := by sorry
