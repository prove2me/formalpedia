-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_finite_distance_locality_of_relativeExpansion
-- name    : QEC.Coding.ExpanderCodes.PK20.finite_distance_locality_of_relativeExpansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:40:26.640876+00:00
-- url     : https://prove2.me/theorems/7af58e9b-0407-436d-94b9-ad345b24d18f
-- title:
--   PK20: finite distance locality of relative Expansion
-- statement:
--   The complete finite handoff from the output vocabulary of PK20 Proposition 1
--   to the source-valid, local, two-sector distance conclusion of Proposition 2.
--   All premises after the two relative expansion statements are elementary
--   containments of the absolute Hamming balls used by the two cases; they will be
--   discharged from the construction scales in the family assembly below.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L316-L402
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L316-L402

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct

theorem QEC.Coding.ExpanderCodes.PK20.finite_distance_locality_of_relativeExpansion
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (forwardDistance transposeDistance w threshold
      radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator lowerBound : Nat)
    (hForwardDistancePositive : 0 < forwardDistance)
    (hTransposeDistancePositive : 0 < transposeDistance)
    (hExpansionNumeratorPositive : 0 < expansionNumerator)
    (hw : 0 < w) (hthreshold : 0 < threshold)
    (hThresholdScale : 2 * w * threshold ≤ q)
    (hForwardWeight : ∀ i : aCol × Cyclic.CyclicGroup q,
      HammingWeight (PKDistance.tannerAction A (Pi.single i 1)) ≤ w)
    (hTransposeWeight : ∀ i : aRow × Cyclic.CyclicGroup q,
      HammingWeight
        (PKDistance.tannerAction (LiftedProduct.starTranspose A)
          (Pi.single i 1)) ≤ w)
    (hForwardRelative :
      (PKDistance.tannerAction A).SmallSetExpandingAtRelativeRadius
        radiusNumerator radiusDenominator
        expansionNumerator expansionDenominator)
    (hTransposeRelative :
      (PKDistance.tannerAction
        (LiftedProduct.starTranspose A)).SmallSetExpandingAtRelativeRadius
          radiusNumerator radiusDenominator
          expansionNumerator expansionDenominator)
    (hForwardCaseOneRadius :
      radiusDenominator * (q * forwardDistance) ≤
        radiusNumerator *
          Fintype.card (aCol × Cyclic.CyclicGroup q))
    (hForwardCaseTwoRadius :
      radiusDenominator * threshold ≤
        radiusNumerator *
          Fintype.card (aCol × Cyclic.CyclicGroup q))
    (hTransposeCaseOneRadius :
      radiusDenominator * (q * transposeDistance) ≤
        radiusNumerator *
          Fintype.card (aRow × Cyclic.CyclicGroup q))
    (hTransposeCaseTwoRadius :
      radiusDenominator * threshold ≤
        radiusNumerator *
          Fintype.card (aRow × Cyclic.CyclicGroup q))
    (hForwardLower :
      max (2 * expansionNumerator) (4 * expansionDenominator) * lowerBound ≤
        expansionNumerator * min (q * forwardDistance) threshold)
    (hTransposeLower :
      max (2 * expansionNumerator) (4 * expansionDenominator) * lowerBound ≤
        expansionNumerator * min (q * transposeDistance) threshold) :
    (LiftedProduct.binaryCSSCode (Cyclic.data q A)).stabilizer.IsSourceValidBinary ∧
      BoundedLocality
        (LiftedProduct.boundaryIncidence
          (Cyclic.data q A)).localityProfile (w + 2) ∧
      MiddleHomologyDistanceAtLeast
        (LiftedProduct.chainComplex (Cyclic.data q A)) lowerBound ∧
      MiddleCohomologyDistanceAtLeast
        (LiftedProduct.chainComplex (Cyclic.data q A)) lowerBound := by sorry
