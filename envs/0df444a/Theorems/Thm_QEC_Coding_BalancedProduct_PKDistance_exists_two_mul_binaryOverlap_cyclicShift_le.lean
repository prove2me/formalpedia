-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_exists_two_mul_binaryOverlap_cyclicShift_le
-- name    : QEC.Coding.BalancedProduct.PKDistance.exists_two_mul_binaryOverlap_cyclicShift_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:02:13.796216+00:00
-- url     : https://prove2.me/theorems/fd606914-6f23-4b93-834e-ae93315eab6c
-- title:
--   PKDistance: exists two mul binary Overlap cyclic Shift le
-- statement:
--   PK20's finite averaging step: some cyclic shift has overlap at most half
--   the total word weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L242-L272
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L242-L272

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

theorem QEC.Coding.BalancedProduct.PKDistance.exists_two_mul_binaryOverlap_cyclicShift_le
    {I : Type u} {G : Type v} [Group G]
    [Fintype I] [Fintype G]
    (z : Word (ZMod 2) (I × G))
    (hhalf : ∀ i, 2 * fibreWeight z i ≤ Fintype.card G) :
    ∃ t : G, 2 * binaryOverlap z (cyclicShift t z) ≤ HammingWeight z := by sorry
