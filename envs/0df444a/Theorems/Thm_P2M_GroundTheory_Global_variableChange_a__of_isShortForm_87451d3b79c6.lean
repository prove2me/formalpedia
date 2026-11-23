-- Prove2me | Theorems.Thm_P2M_GroundTheory_Global_variableChange_a__of_isShortForm_87451d3b79c6
-- name    : P2M_GroundTheory_Global_variableChange_a__of_isShortForm_87451d3b79c6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:35.53639+00:00
-- url     : https://prove2.me/theorems/3ce6229f-7912-47a2-8c00-5a69c182b792
-- title:
--   P2 M Ground Theory Global variable Change a  of is Short Form 87451d3b79c6: P2 M Ground Theory Global variable Change a  of is Short Form 87451d3b79c6
-- statement:
--   The P2 M Ground Theory Global variable Change a  of is Short Form 87451d3b79c6 construction uses the P2 M Ground Theory Global variable Change a  of is Short Form 87451d3b79c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunction.lean#L96-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunction.lean#L96-L99

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

theorem P2M_GroundTheory_Global_variableChange_a__of_isShortForm_87451d3b79c6 {C : VariableChange F} {W : WeierstrassCurve F}
    (hW : IsShortForm W) (hCW : IsShortForm (C • W)) : (C • W).a₆ = ↑C.u⁻¹ ^ 6 * W.a₆ := by sorry

alias «GroundTheory».«Global».«variableChange_a₆_of_isShortForm» := P2M_GroundTheory_Global_variableChange_a__of_isShortForm_87451d3b79c6
