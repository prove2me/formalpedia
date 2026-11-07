-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_nonzero_horizontalClass_caseOne_weight_bound_distanceLowerBound
-- name    : QEC.Coding.BalancedProduct.PKDistance.nonzero_horizontalClass_caseOne_weight_bound_distanceLowerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:06:12.804266+00:00
-- url     : https://prove2.me/theorems/3b85a6af-970f-438f-8eb6-95b2272f13dc
-- title:
--   PKDistance: nonzero horizontal Class case One weight bound distance Lower Bound
-- statement:
--   The PKDistance construction uses the nonzero horizontal Class case One weight bound distance Lower Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L2772-L2838
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L2772-L2838

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

theorem QEC.Coding.BalancedProduct.PKDistance.nonzero_horizontalClass_caseOne_weight_bound_distanceLowerBound
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleCycleCode.carrier)
    {actualDistance distanceLowerBound : Nat}
    (hMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex A).middleCycleCode
        actualDistance)
    (hDistanceLower : distanceLowerBound ≤ actualDistance)
    (hProjected : HorizontalSubsystem.horizontalHomologyProjection A
      (Cyclic.cyclicGenerator q)
      ((LiftedProduct.chainComplex
        (Cyclic.data q A)).middleBoundaryInCycles.mkQ ⟨z, hz⟩) ≠ 0)
    (expansionNumerator expansionDenominator : Nat)
    (hLowerPositive : 0 < distanceLowerBound)
    (hExpansion : (tannerAction A).SmallSetExpanding
      (q * distanceLowerBound) expansionNumerator expansionDenominator) :
    expansionNumerator * (q * distanceLowerBound) ≤
      max (2 * expansionNumerator) (4 * expansionDenominator) *
        HammingWeight z := by sorry
