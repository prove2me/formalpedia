-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_tLine_not_mem_bot_4c07bc61bfd4
-- name    : P2M_GroundTheory_Heights__Heights_linForm_tLine_not_mem_bot_4c07bc61bfd4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:47:43.67667+00:00
-- url     : https://prove2.me/theorems/d84cafbd-1fdb-4bc1-83e1-d8985c1a4ff6
-- title:
--   P2 M Ground Theory Heights  Heights lin Form t Line not mem bot 4c07bc61bfd4: P2 M Ground Theory Heights  Heights lin Form t Line not mem bot 4c07bc61bfd4
-- statement:
--   The P2 M Ground Theory Heights  Heights lin Form t Line not mem bot 4c07bc61bfd4 construction uses the P2 M Ground Theory Heights  Heights lin Form t Line not mem bot 4c07bc61bfd4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsSectionOrder.lean#L215-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsSectionOrder.lean#L215-L217

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
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
open MvPolynomial
noncomputable section
open LineChowForm

theorem P2M_GroundTheory_Heights__Heights_linForm_tLine_not_mem_bot_4c07bc61bfd4 : linForm tLine ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«linForm_tLine_not_mem_bot» := P2M_GroundTheory_Heights__Heights_linForm_tLine_not_mem_bot_4c07bc61bfd4
