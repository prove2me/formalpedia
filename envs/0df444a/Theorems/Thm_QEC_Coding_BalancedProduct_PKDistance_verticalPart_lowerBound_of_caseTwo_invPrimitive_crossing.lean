-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_verticalPart_lowerBound_of_caseTwo_invPrimitive_crossing
-- name    : QEC.Coding.BalancedProduct.PKDistance.verticalPart_lowerBound_of_caseTwo_invPrimitive_crossing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:05:06.042575+00:00
-- url     : https://prove2.me/theorems/377ef17d-655e-4859-88fa-44c2e1f2be1b
-- title:
--   PKDistance: vertical Part lower Bound of case Two inv Primitive crossing
-- statement:
--   Quantitative Case-2 expansion core in the inverse cyclic orientation used
--   by the dual lifted product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1443-L1499
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1443-L1499

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

theorem QEC.Coding.BalancedProduct.PKDistance.verticalPart_lowerBound_of_caseTwo_invPrimitive_crossing
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit
        (Cyclic.CyclicGroup q)))
    (hz : LiftedProduct.boundary1
      (Cyclic.liftedProductData A (Cyclic.cyclicGenerator q)⁻¹) z = 0)
    (h : Word (ZMod 2) (aCol × Cyclic.CyclicGroup q))
    (hu : horizontalPart z =
      h + cyclicShift (Cyclic.cyclicGenerator q)⁻¹ h)
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
