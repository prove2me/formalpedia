-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_classicalFactorCertificate_of_propositionOne_output
-- name    : QEC.Coding.ExpanderCodes.PK20.classicalFactorCertificate_of_propositionOne_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:25:27.485233+00:00
-- url     : https://prove2.me/theorems/9772afa4-67a3-41d2-b052-554704389ca6
-- title:
--   PK20: classical Factor Certificate of proposition One output
-- statement:
--   The Proposition 1 Tanner matrix gives a surjective, constant-locality,
--   linear-distance classical boundary after deleting dependent rows.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ClassicalFactor.lean#L153-L202
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ClassicalFactor.lean#L153-L202

import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear
import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalRowReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalFactor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct
open QEC.Coding.DistanceBalancing

theorem QEC.Coding.ExpanderCodes.PK20.classicalFactorCertificate_of_propositionOne_output
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (w radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : Nat)
    (hExpansionNumerator : 0 < expansionNumerator)
    (hForwardWeight : ∀ i : aCol × Cyclic.CyclicGroup q,
      HammingWeight (PKDistance.tannerAction A (Pi.single i 1)) ≤ w)
    (hTransposeWeight : ∀ i : aRow × Cyclic.CyclicGroup q,
      HammingWeight
        (PKDistance.tannerAction (LiftedProduct.starTranspose A)
          (Pi.single i 1)) ≤ w)
    (hForwardRelative :
      (PKDistance.tannerAction A).SmallSetExpandingAtRelativeRadius
        radiusNumerator radiusDenominator
        expansionNumerator expansionDenominator) :
    ClassicalFactorCertificate (PKDistance.tannerAction A)
      (classicalDistanceLowerBound
        (Fintype.card (aCol × Cyclic.CyclicGroup q))
        radiusNumerator radiusDenominator) w := by sorry
