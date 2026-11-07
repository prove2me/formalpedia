-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_exists_invCyclicPower_HammingWeight_le_add_shift
-- name    : QEC.Coding.BalancedProduct.PKDistance.exists_invCyclicPower_HammingWeight_le_add_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:02:20.052769+00:00
-- url     : https://prove2.me/theorems/f7a55df0-07d2-47c6-a414-dbe06e54d4c0
-- title:
--   PKDistance: exists inv Cyclic Power Hamming Weight le add shift
-- statement:
--   Opposite-orientation canonical-index form of the autocorrelation lemma.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L315-L332
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L315-L332

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

theorem QEC.Coding.BalancedProduct.PKDistance.exists_invCyclicPower_HammingWeight_le_add_shift
    {I : Type u} [Fintype I]
    (q : Nat) [NeZero q]
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hhalf : ∀ i, 2 * fibreWeight z i ≤ q) :
    ∃ t < q, HammingWeight z ≤ HammingWeight
      (z + cyclicShift ((Cyclic.cyclicGenerator q)⁻¹ ^ t) z) := by sorry
