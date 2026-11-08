-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_twiceBalancedMemberCertificate
-- name    : QEC.Coding.ExpanderCodes.PK20.twiceBalancedMemberCertificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:38:31.444938+00:00
-- url     : https://prove2.me/theorems/1acd63d1-2ccf-41c7-ab06-ae3016394079
-- title:
--   PK20: twice Balanced Member Certificate
-- statement:
--   Complete finite EKZ closure used by PK20 Theorem 2.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TwoStepBalancing.lean#L295-L345
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TwoStepBalancing.lean#L295-L345

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_ExpanderCodes_TwoStepBalancing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.DistanceBalancing
universe u
variable {xZero xOne xTwo bitOne checkOne bitTwo checkTwo : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype bitOne] [DecidableEq bitOne]
variable [Fintype checkOne] [DecidableEq checkOne]
variable [Fintype bitTwo] [DecidableEq bitTwo]
variable [Fintype checkTwo] [DecidableEq checkTwo]

theorem QEC.Coding.ExpanderCodes.PK20.twiceBalancedMemberCertificate
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y₁ : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne)
    (Y₂ : Word (ZMod 2) bitTwo →ₗ[ZMod 2] Word (ZMod 2) checkTwo)
    {sourceDimension classicalDimensionOne classicalDimensionTwo
      sourceDistance classicalDistanceOne classicalDistanceTwo
      sourceLocality classicalLocalityOne classicalLocalityTwo : Nat}
    (hSourceDimension : sourceDimension ≤
      Module.finrank (ZMod 2) X.middleHomology)
    (hClassicalDimensionOne : classicalDimensionOne ≤
      Module.finrank (ZMod 2) (LinearMap.ker Y₁))
    (hClassicalDimensionTwo : classicalDimensionTwo ≤
      Module.finrank (ZMod 2) (LinearMap.ker Y₂))
    (hSurjectiveOne : Function.Surjective Y₁)
    (hSurjectiveTwo : Function.Surjective Y₂)
    (hHomology : MiddleHomologyDistanceAtLeast X sourceDistance)
    (hCohomology : MiddleCohomologyDistanceAtLeast X sourceDistance)
    (hClassicalOne : ClassicalDistanceAtLeast
      (LinearMap.toMatrix' Y₁) classicalDistanceOne)
    (hClassicalTwo : ClassicalDistanceAtLeast
      (LinearMap.toMatrix' Y₂) classicalDistanceTwo)
    (hSourceLocality : BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X).localityProfile sourceLocality)
    (hRowOne : ∀ b, HammingWeight
      (wordLinearMapTranspose Y₁ (Pi.single b 1)) ≤ classicalLocalityOne)
    (hColumnOne : ∀ a, HammingWeight
      (Y₁ (Pi.single a 1)) ≤ classicalLocalityOne)
    (hRowTwo : ∀ b, HammingWeight
      (wordLinearMapTranspose Y₂ (Pi.single b 1)) ≤ classicalLocalityTwo)
    (hColumnTwo : ∀ a, HammingWeight
      (Y₂ (Pi.single a 1)) ≤ classicalLocalityTwo) :
    TwiceBalancedMemberCertificate X Y₁ Y₂
      sourceDimension classicalDimensionOne classicalDimensionTwo
      sourceDistance classicalDistanceOne classicalDistanceTwo
      (sourceLocality + classicalLocalityOne + classicalLocalityTwo) := by sorry
