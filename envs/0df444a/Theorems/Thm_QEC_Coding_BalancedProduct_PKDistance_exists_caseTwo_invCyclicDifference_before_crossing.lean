-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_exists_caseTwo_invCyclicDifference_before_crossing
-- name    : QEC.Coding.BalancedProduct.PKDistance.exists_caseTwo_invCyclicDifference_before_crossing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:04:53.029295+00:00
-- url     : https://prove2.me/theorems/362a7b8b-330a-4375-901b-fad43ca1fed1
-- title:
--   PKDistance: exists case Two inv Cyclic Difference before crossing
-- statement:
--   First-crossing theorem in the opposite cyclic orientation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1339-L1379
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1339-L1379

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

theorem QEC.Coding.BalancedProduct.PKDistance.exists_caseTwo_invCyclicDifference_before_crossing
    {I : Type u} [Fintype I]
    (q : Nat) [NeZero q]
    (h : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hhalf : ∀ i, 2 * fibreWeight h i ≤ q)
    (threshold : Nat) (hthreshold : 0 < threshold)
    (hPrimitive : threshold ≤ HammingWeight h) :
    ∃ t < q,
      HammingWeight
          (h + cyclicShift ((Cyclic.cyclicGenerator q)⁻¹ ^ t) h) < threshold ∧
      threshold ≤ HammingWeight
          (h + cyclicShift ((Cyclic.cyclicGenerator q)⁻¹ ^ (t + 1)) h) ∧
      threshold ≤ HammingWeight
          (h + cyclicShift ((Cyclic.cyclicGenerator q)⁻¹ ^ t) h) +
        HammingWeight
          (h + cyclicShift (Cyclic.cyclicGenerator q)⁻¹ h) := by sorry
