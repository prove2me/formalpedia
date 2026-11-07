-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclic_card_le_HammingWeight_of_invInvariant_ne_zero
-- name    : QEC.Coding.BalancedProduct.PKDistance.cyclic_card_le_HammingWeight_of_invInvariant_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:04:56.303766+00:00
-- url     : https://prove2.me/theorems/9ef3a230-259a-42c9-b8f5-b2571bee4f8f
-- title:
--   PKDistance: cyclic card le Hamming Weight of inv Invariant ne zero
-- statement:
--   Invariance under the inverse canonical generator has the same full-fibre
--   weight consequence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1074-L1097
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1074-L1097

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

theorem QEC.Coding.BalancedProduct.PKDistance.cyclic_card_le_HammingWeight_of_invInvariant_ne_zero
    {I : Type u} [Fintype I]
    (q : Nat) [NeZero q]
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hzero : z + cyclicShift (Cyclic.cyclicGenerator q)⁻¹ z = 0)
    (hne : z ≠ 0) :
    q ≤ HammingWeight z := by sorry
