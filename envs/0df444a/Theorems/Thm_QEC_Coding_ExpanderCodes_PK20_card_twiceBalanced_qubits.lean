-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_card_twiceBalanced_qubits
-- name    : QEC.Coding.ExpanderCodes.PK20.card_twiceBalanced_qubits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:34:30.853562+00:00
-- url     : https://prove2.me/theorems/e34ccac9-e9cb-4030-acb9-25633fb8e502
-- title:
--   PK20: card twice Balanced qubits
-- statement:
--   Exact number of physical qubits after the two PK20 homological products.
--   It is recorded before any asymptotic estimates, so neither product may hide a
--   change of family scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TwoStepBalancing.lean#L86-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TwoStepBalancing.lean#L86-L100

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

theorem QEC.Coding.ExpanderCodes.PK20.card_twiceBalanced_qubits
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y₁ : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne)
    (Y₂ : Word (ZMod 2) bitTwo →ₗ[ZMod 2] Word (ZMod 2) checkTwo) :
    Fintype.card
        (SecondQubit xZero xOne xTwo bitOne checkOne bitTwo checkTwo) =
      (Fintype.card xOne * Fintype.card bitOne +
          Fintype.card xTwo * Fintype.card checkOne) *
        Fintype.card bitTwo +
      (Fintype.card xZero * Fintype.card bitOne +
          Fintype.card xOne * Fintype.card checkOne) *
        Fintype.card checkTwo := by sorry
