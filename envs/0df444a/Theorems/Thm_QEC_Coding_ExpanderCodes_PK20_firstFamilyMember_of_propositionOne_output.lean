-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_firstFamilyMember_of_propositionOne_output
-- name    : QEC.Coding.ExpanderCodes.PK20.firstFamilyMember_of_propositionOne_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:40:24.165219+00:00
-- url     : https://prove2.me/theorems/dd8c8eb1-a379-4f63-9ccb-2733f6f09f51
-- title:
--   PK20: first Family Member of proposition One output
-- statement:
--   Complete finite construction from the raw output of PK20 Proposition 1.
--   The two elementary scale conditions merely say that the selected cyclic lift
--   is beyond the fixed constants of that proposition; the family assembly below
--   selects such odd lifts cofinally.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L777-L933
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean#L777-L933

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct

theorem QEC.Coding.ExpanderCodes.PK20.firstFamilyMember_of_propositionOne_output
    (w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator q n m : Nat)
    [NeZero q]
    (A : Matrix (Fin m) (Fin (w * n))
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (hw4 : 4 ≤ w)
    (hgamma : 0 < gamma)
    (hRadiusNumerator : 0 < radiusNumerator)
    (hRadiusDenominator : 0 < radiusDenominator)
    (hExpansionNumerator : 0 < expansionNumerator)
    (hExpansionDenominator : 0 < expansionDenominator)
    (hqOdd : Odd q)
    (hm : m = 2 * (w / 4) * n)
    (hnLower : gamma * Nat.log 2 q ≤ n)
    (hnUpper : n ≤ gamma * (Nat.log 2 q + 1))
    (hDenominatorLeN : radiusDenominator ≤ n)
    (hLiftLarge : 2 * w * radiusDenominator ≤ q)
    (hForwardWeight : ∀ i : Fin (w * n) × Cyclic.CyclicGroup q,
      HammingWeight (PKDistance.tannerAction A (Pi.single i 1)) ≤ w)
    (hTransposeWeight : ∀ i : Fin m × Cyclic.CyclicGroup q,
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
          expansionNumerator expansionDenominator) :
    FirstFamilyMember w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator q n m A := by sorry
