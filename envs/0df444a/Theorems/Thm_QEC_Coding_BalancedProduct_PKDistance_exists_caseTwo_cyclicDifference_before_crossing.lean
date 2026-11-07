-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_exists_caseTwo_cyclicDifference_before_crossing
-- name    : QEC.Coding.BalancedProduct.PKDistance.exists_caseTwo_cyclicDifference_before_crossing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:05:00.462649+00:00
-- url     : https://prove2.me/theorems/2f220770-d04e-4999-a9e7-cdf07fba02bc
-- title:
--   PKDistance: exists case Two cyclic Difference before crossing
-- statement:
--   Source-exact first crossing for the Case-2 differences
--   `(1+x^t)h`.  The endpoint is supplied by the indexed autocorrelation lemma,
--   and each step has exactly the concrete horizontal weight `|(1+x)h|`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1293-L1336
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1293-L1336

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

theorem QEC.Coding.BalancedProduct.PKDistance.exists_caseTwo_cyclicDifference_before_crossing
    {I : Type u} [Fintype I]
    (q : Nat) [NeZero q]
    (h : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hhalf : ∀ i, 2 * fibreWeight h i ≤ q)
    (threshold : Nat) (hthreshold : 0 < threshold)
    (hPrimitive : threshold ≤ HammingWeight h) :
    ∃ t < q,
      HammingWeight
          (h + cyclicShift (Cyclic.cyclicGenerator q ^ t) h) < threshold ∧
      threshold ≤ HammingWeight
          (h + cyclicShift (Cyclic.cyclicGenerator q ^ (t + 1)) h) ∧
      threshold ≤
        HammingWeight (h + cyclicShift (Cyclic.cyclicGenerator q ^ t) h) +
          HammingWeight (h + cyclicShift (Cyclic.cyclicGenerator q) h) := by sorry
