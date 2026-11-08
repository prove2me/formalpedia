-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_twiceBalanced_distanceBounds
-- name    : QEC.Coding.ExpanderCodes.PK20.twiceBalanced_distanceBounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:38:05.813786+00:00
-- url     : https://prove2.me/theorems/d6b0596b-cd59-4822-895b-5f8ebd96e4b4
-- title:
--   PK20: twice Balanced distance Bounds
-- statement:
--   Both distances after the two products and the two orientation reversals.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TwoStepBalancing.lean#L127-L169
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TwoStepBalancing.lean#L127-L169

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

theorem QEC.Coding.ExpanderCodes.PK20.twiceBalanced_distanceBounds
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y₁ : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne)
    (Y₂ : Word (ZMod 2) bitTwo →ₗ[ZMod 2] Word (ZMod 2) checkTwo)
    {dHomology dCohomology dClassicalOne dClassicalTwo : Nat}
    (hSurjectiveOne : Function.Surjective Y₁)
    (hSurjectiveTwo : Function.Surjective Y₂)
    (hHomology : MiddleHomologyDistanceAtLeast X dHomology)
    (hCohomology : MiddleCohomologyDistanceAtLeast X dCohomology)
    (hClassicalOne : ClassicalDistanceAtLeast
      (LinearMap.toMatrix' Y₁) dClassicalOne)
    (hClassicalTwo : ClassicalDistanceAtLeast
      (LinearMap.toMatrix' Y₂) dClassicalTwo) :
    MiddleHomologyDistanceAtLeast (twiceBalancedComplex X Y₁ Y₂)
        (dClassicalOne * dHomology) ∧
      MiddleCohomologyDistanceAtLeast (twiceBalancedComplex X Y₁ Y₂)
        (dClassicalTwo * dCohomology) := by sorry
