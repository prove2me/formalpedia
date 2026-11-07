-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_nonzero_horizontalCohomologyClass_cases_weight_bound_of_expansion
-- name    : QEC.Coding.BalancedProduct.PKDistance.nonzero_horizontalCohomologyClass_cases_weight_bound_of_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:06:41.258939+00:00
-- url     : https://prove2.me/theorems/efb55bf4-ef13-409c-a50f-e3e784d1cd90
-- title:
--   PKDistance: nonzero horizontal Cohomology Class cases weight bound of expansion
-- statement:
--   The dual PK case split needs no global assertion that the quotient dual
--   code is nonzero: a nonzero projected class produces its own attained minimum,
--   while a zero projected class is handled directly by Case 2.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L3114-L3205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L3114-L3205

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

theorem QEC.Coding.BalancedProduct.PKDistance.nonzero_horizontalCohomologyClass_cases_weight_bound_of_expansion
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleCocycleCode.carrier)
    (hProjected : HorizontalSubsystem.horizontalCohomologyProjection A
      (Cyclic.cyclicGenerator q)
      ((LiftedProduct.chainComplex
        (Cyclic.data q A)).middleCoboundaryInCocycles.mkQ ⟨z, hz⟩) ≠ 0)
    (dualDistanceLowerBound : Nat)
    (hDualDistanceLowerPositive : 0 < dualDistanceLowerBound)
    (w threshold expansionRadius expansionNumerator expansionDenominator : Nat)
    (hExpansionNumeratorPositive : 0 < expansionNumerator)
    (hw : 0 < w) (hthreshold : 0 < threshold)
    (hThresholdScale : 2 * w * threshold ≤ q)
    (hColumnWeight : ∀ i : aRow × Cyclic.CyclicGroup q,
      HammingWeight
        (tannerAction (LiftedProduct.starTranspose A) (Pi.single i 1)) ≤ w)
    (hRadius : threshold ≤ expansionRadius)
    (hCaseOneExpansion :
      (tannerAction (LiftedProduct.starTranspose A)).SmallSetExpanding
        (q * dualDistanceLowerBound) expansionNumerator expansionDenominator)
    (hCaseTwoExpansion :
      (tannerAction (LiftedProduct.starTranspose A)).SmallSetExpanding
        expansionRadius expansionNumerator expansionDenominator) :
    expansionNumerator * min (q * dualDistanceLowerBound) threshold ≤
      max (2 * expansionNumerator) (4 * expansionDenominator) *
        HammingWeight z := by sorry
