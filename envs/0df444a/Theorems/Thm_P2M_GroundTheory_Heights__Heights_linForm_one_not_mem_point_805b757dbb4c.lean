-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_one_not_mem_point_805b757dbb4c
-- name    : P2M_GroundTheory_Heights__Heights_linForm_one_not_mem_point_805b757dbb4c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:04.631938+00:00
-- url     : https://prove2.me/theorems/8cd7c4ce-f6b4-46a3-8431-0a598beb9145
-- title:
--   P2 M Ground Theory Heights  Heights lin Form one not mem point 805b757dbb4c: P2 M Ground Theory Heights  Heights lin Form one not mem point 805b757dbb4c
-- statement:
--   The P2 M Ground Theory Heights  Heights lin Form one not mem point 805b757dbb4c construction uses the P2 M Ground Theory Heights  Heights lin Form one not mem point 805b757dbb4c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L335-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L335-L338

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_linForm_one_not_mem_point_805b757dbb4c (F : Type*) [Field F] :
    linForm (fun _ => (1 : F)) ∉ (⊥ : Ideal (MvPolynomial (Fin 1) F)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«linForm_one_not_mem_point» := P2M_GroundTheory_Heights__Heights_linForm_one_not_mem_point_805b757dbb4c
