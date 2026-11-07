-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_exists_cyclicPower_HammingWeight_le_add_shift
-- name    : QEC.Coding.BalancedProduct.PKDistance.exists_cyclicPower_HammingWeight_le_add_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:02:19.388193+00:00
-- url     : https://prove2.me/theorems/b8346e40-ca3e-4b3f-a7c0-215e8ff03722
-- title:
--   PKDistance: exists cyclic Power Hamming Weight le add shift
-- statement:
--   Canonical-index form of the autocorrelation lemma: the witnessing
--   translation is a generator power with exponent strictly below `q`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L295-L312
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L295-L312

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

theorem QEC.Coding.BalancedProduct.PKDistance.exists_cyclicPower_HammingWeight_le_add_shift
    {I : Type u} [Fintype I]
    (q : Nat) [NeZero q]
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hhalf : ∀ i, 2 * fibreWeight z i ≤ q) :
    ∃ t < q, HammingWeight z ≤ HammingWeight
      (z + cyclicShift (Cyclic.cyclicGenerator q ^ t) z) := by sorry
