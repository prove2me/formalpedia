-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_zero_horizontalClass_caseTwo_weight_bound
-- name    : QEC.Coding.BalancedProduct.PKDistance.zero_horizontalClass_caseTwo_weight_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:23:29.168371+00:00
-- url     : https://prove2.me/theorems/d53c0e5f-144f-4c5b-bc5c-7eee283c65aa
-- title:
--   PKDistance: zero horizontal Class case Two weight bound
-- statement:
--   Source-shaped completion of PK20 Proposition 2, Case 2 for an actual
--   non-boundary cycle whose horizontal quotient class vanishes.  The scale
--   condition `2*w*threshold <= q` is the exact integer form used to derive the
--   primitive crossing threshold from the full cyclic remainder.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1866-L1969
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1866-L1969

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

theorem QEC.Coding.BalancedProduct.PKDistance.zero_horizontalClass_caseTwo_weight_bound
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit
        (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleCycleCode.carrier)
    (hzNotBoundary : z ∉ (LiftedProduct.chainComplex
      (Cyclic.data q A)).middleBoundaryCode.carrier)
    (hProjected : HorizontalSubsystem.horizontalHomologyProjection A
      (Cyclic.cyclicGenerator q)
      ((LiftedProduct.chainComplex
        (Cyclic.data q A)).middleBoundaryInCycles.mkQ ⟨z, hz⟩) = 0)
    (w threshold expansionRadius expansionNumerator expansionDenominator : Nat)
    (hw : 0 < w) (hthreshold : 0 < threshold)
    (hThresholdScale : 2 * w * threshold ≤ q)
    (hColumnWeight : ∀ i : aCol × Cyclic.CyclicGroup q,
      HammingWeight (tannerAction A (Pi.single i 1)) ≤ w)
    (hRadius : threshold ≤ expansionRadius)
    (hExpansion : (tannerAction A).SmallSetExpanding
      expansionRadius expansionNumerator expansionDenominator) :
    expansionNumerator * threshold ≤
      max (2 * expansionNumerator) (4 * expansionDenominator) *
        HammingWeight z := by sorry
