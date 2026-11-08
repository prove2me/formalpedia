-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_twiceBalanced_boundedLocality
-- name    : QEC.Coding.ExpanderCodes.PK20.twiceBalanced_boundedLocality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:38:28.226521+00:00
-- url     : https://prove2.me/theorems/81fe2df1-a764-4e96-81d1-a2891ac5d576
-- title:
--   PK20: twice Balanced bounded Locality
-- statement:
--   Uniform locality grows only by the two classical locality constants.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TwoStepBalancing.lean#L226-L253
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TwoStepBalancing.lean#L226-L253

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

theorem QEC.Coding.ExpanderCodes.PK20.twiceBalanced_boundedLocality
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y₁ : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne)
    (Y₂ : Word (ZMod 2) bitTwo →ₗ[ZMod 2] Word (ZMod 2) checkTwo)
    {sourceBound classicalBoundOne classicalBoundTwo : Nat}
    (hSource : BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X).localityProfile sourceBound)
    (hRowOne : ∀ b, HammingWeight
      (wordLinearMapTranspose Y₁ (Pi.single b 1)) ≤ classicalBoundOne)
    (hColumnOne : ∀ a, HammingWeight
      (Y₁ (Pi.single a 1)) ≤ classicalBoundOne)
    (hRowTwo : ∀ b, HammingWeight
      (wordLinearMapTranspose Y₂ (Pi.single b 1)) ≤ classicalBoundTwo)
    (hColumnTwo : ∀ a, HammingWeight
      (Y₂ (Pi.single a 1)) ≤ classicalBoundTwo) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (twiceBalancedComplex X Y₁ Y₂)).localityProfile
      (sourceBound + classicalBoundOne + classicalBoundTwo) := by sorry
