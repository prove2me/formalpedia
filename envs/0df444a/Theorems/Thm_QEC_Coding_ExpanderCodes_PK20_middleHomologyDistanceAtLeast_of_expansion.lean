-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_middleHomologyDistanceAtLeast_of_expansion
-- name    : QEC.Coding.ExpanderCodes.PK20.middleHomologyDistanceAtLeast_of_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:40:16.883334+00:00
-- url     : https://prove2.me/theorems/cccfaf1e-fd4e-4518-a342-1c0b40e12a32
-- title:
--   PK20: middle Homology Distance At Least of expansion
-- statement:
--   PK20 Proposition 2 for ordinary middle homology.  The two expansion
--   hypotheses are the source's Case 1 quotient-distance radius and Case 2
--   primitive-crossing radius.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L94-L163
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L94-L163

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct

theorem QEC.Coding.ExpanderCodes.PK20.middleHomologyDistanceAtLeast_of_expansion
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (distanceLowerBound w threshold expansionRadius
      expansionNumerator expansionDenominator lowerBound : Nat)
    (hDistancePositive : 0 < distanceLowerBound)
    (hExpansionNumeratorPositive : 0 < expansionNumerator)
    (hw : 0 < w) (hthreshold : 0 < threshold)
    (hThresholdScale : 2 * w * threshold ≤ q)
    (hColumnWeight : ∀ i : aCol × Cyclic.CyclicGroup q,
      HammingWeight (PKDistance.tannerAction A (Pi.single i 1)) ≤ w)
    (hRadius : threshold ≤ expansionRadius)
    (hCaseOneExpansion :
      (PKDistance.tannerAction A).SmallSetExpanding
        (q * distanceLowerBound) expansionNumerator expansionDenominator)
    (hCaseTwoExpansion :
      (PKDistance.tannerAction A).SmallSetExpanding
        expansionRadius expansionNumerator expansionDenominator)
    (hLowerBound :
      max (2 * expansionNumerator) (4 * expansionDenominator) * lowerBound ≤
        expansionNumerator * min (q * distanceLowerBound) threshold) :
    MiddleHomologyDistanceAtLeast
      (LiftedProduct.chainComplex (Cyclic.data q A)) lowerBound := by sorry
