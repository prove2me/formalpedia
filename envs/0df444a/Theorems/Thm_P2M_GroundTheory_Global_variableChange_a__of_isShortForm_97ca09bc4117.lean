-- Prove2me | Theorems.Thm_P2M_GroundTheory_Global_variableChange_a__of_isShortForm_97ca09bc4117
-- name    : P2M_GroundTheory_Global_variableChange_a__of_isShortForm_97ca09bc4117
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:54.388846+00:00
-- url     : https://prove2.me/theorems/3d4ca1b2-5fff-4dfe-9782-a92f35b33d16
-- title:
--   P2 M Ground Theory Global variable Change a  of is Short Form 97ca09bc4117: P2 M Ground Theory Global variable Change a  of is Short Form 97ca09bc4117
-- statement:
--   The P2 M Ground Theory Global variable Change a  of is Short Form 97ca09bc4117 construction uses the P2 M Ground Theory Global variable Change a  of is Short Form 97ca09bc4117 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunction.lean#L91-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunction.lean#L91-L94

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_VariableChangePoints
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open WeierstrassCurve OnePoint
variable {F : Type*} [Field F]
open ShortWeierstrass
variable [CharZero F]

theorem P2M_GroundTheory_Global_variableChange_a__of_isShortForm_97ca09bc4117 {C : VariableChange F} {W : WeierstrassCurve F}
    (hW : IsShortForm W) (hCW : IsShortForm (C • W)) : (C • W).a₄ = ↑C.u⁻¹ ^ 4 * W.a₄ := by sorry

alias «GroundTheory».«Global».«variableChange_a₄_of_isShortForm» := P2M_GroundTheory_Global_variableChange_a__of_isShortForm_97ca09bc4117
