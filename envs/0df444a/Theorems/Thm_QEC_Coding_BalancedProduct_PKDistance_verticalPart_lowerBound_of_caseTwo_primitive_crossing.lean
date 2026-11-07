-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_verticalPart_lowerBound_of_caseTwo_primitive_crossing
-- name    : QEC.Coding.BalancedProduct.PKDistance.verticalPart_lowerBound_of_caseTwo_primitive_crossing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:05:15.023368+00:00
-- url     : https://prove2.me/theorems/46d2a690-e84a-4275-9651-5db94157ce20
-- title:
--   PKDistance: vertical Part lower Bound of case Two primitive crossing
-- statement:
--   Quantitative core of PK20 Proposition 2, Case 2.  Once the normalized
--   primitive reaches `threshold`, expansion and cancellation of the constant
--   remainder force the concrete vertical block to be large.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1384-L1439
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1384-L1439

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

theorem QEC.Coding.BalancedProduct.PKDistance.verticalPart_lowerBound_of_caseTwo_primitive_crossing
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit
        (Cyclic.CyclicGroup q)))
    (hz : LiftedProduct.boundary1 (Cyclic.data q A) z = 0)
    (h : Word (ZMod 2) (aCol × Cyclic.CyclicGroup q))
    (hu : horizontalPart z =
      h + cyclicShift (Cyclic.cyclicGenerator q) h)
    (hhalf : ∀ i, 2 * fibreWeight h i ≤ q)
    (threshold expansionRadius expansionNumerator expansionDenominator : Nat)
    (hthreshold : 0 < threshold)
    (hPrimitive : threshold ≤ HammingWeight h)
    (hRadius : threshold ≤ expansionRadius)
    (hExpansion : (tannerAction A).SmallSetExpanding
      expansionRadius expansionNumerator expansionDenominator) :
    expansionNumerator *
        (threshold - HammingWeight (horizontalPart z)) ≤
      2 * expansionDenominator * HammingWeight (verticalPart z) := by sorry
