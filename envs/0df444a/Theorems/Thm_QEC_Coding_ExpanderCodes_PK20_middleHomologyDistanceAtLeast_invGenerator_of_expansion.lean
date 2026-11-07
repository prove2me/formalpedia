-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_middleHomologyDistanceAtLeast_invGenerator_of_expansion
-- name    : QEC.Coding.ExpanderCodes.PK20.middleHomologyDistanceAtLeast_invGenerator_of_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:39:49.087198+00:00
-- url     : https://prove2.me/theorems/6e60f357-2722-4477-add9-f12561d28f33
-- title:
--   PK20: middle Homology Distance At Least inv Generator of expansion
-- statement:
--   Inverse-orientation form of the full PK20 homology-distance argument.
--   This is the form reached after dualizing a cocycle of `LP(A,1+x)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L167-L240
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L167-L240

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct

theorem QEC.Coding.ExpanderCodes.PK20.middleHomologyDistanceAtLeast_invGenerator_of_expansion
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
      (LiftedProduct.chainComplex
        (Cyclic.liftedProductData A (Cyclic.cyclicGenerator q)⁻¹))
      lowerBound := by sorry
