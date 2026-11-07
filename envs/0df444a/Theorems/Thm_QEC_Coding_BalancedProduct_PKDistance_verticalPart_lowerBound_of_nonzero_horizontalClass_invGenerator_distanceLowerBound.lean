-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_verticalPart_lowerBound_of_nonzero_horizontalClass_invGenerator_distanceLowerBound
-- name    : QEC.Coding.BalancedProduct.PKDistance.verticalPart_lowerBound_of_nonzero_horizontalClass_invGenerator_distanceLowerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:06:35.036382+00:00
-- url     : https://prove2.me/theorems/3f139153-74a8-471b-abf3-89aebb4acf29
-- title:
--   PKDistance: vertical Part lower Bound of nonzero horizontal Class inv Generator distance Lower Bound
-- statement:
--   The PKDistance construction uses the vertical Part lower Bound of nonzero horizontal Class inv Generator distance Lower Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L2723-L2770
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L2723-L2770

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

theorem QEC.Coding.BalancedProduct.PKDistance.verticalPart_lowerBound_of_nonzero_horizontalClass_invGenerator_distanceLowerBound
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData A
        (Cyclic.cyclicGenerator q)⁻¹)).middleCycleCode.carrier)
    {actualDistance distanceLowerBound : Nat}
    (hMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex A).middleCycleCode
        actualDistance)
    (hDistanceLower : distanceLowerBound ≤ actualDistance)
    (hProjected : HorizontalSubsystem.horizontalHomologyProjection A
      (Cyclic.cyclicGenerator q)⁻¹
      ((LiftedProduct.chainComplex
        (Cyclic.liftedProductData A
          (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryInCycles.mkQ
            ⟨z, hz⟩) ≠ 0)
    (stepBound expansionNumerator expansionDenominator : Nat)
    (hLowerPositive : 0 < distanceLowerBound)
    (hstepBound : HammingWeight (horizontalPart z) ≤ stepBound)
    (hExpansion : (tannerAction A).SmallSetExpanding
      (q * distanceLowerBound) expansionNumerator expansionDenominator) :
    expansionNumerator * (q * distanceLowerBound - stepBound) ≤
      2 * expansionDenominator * HammingWeight (verticalPart z) := by sorry
