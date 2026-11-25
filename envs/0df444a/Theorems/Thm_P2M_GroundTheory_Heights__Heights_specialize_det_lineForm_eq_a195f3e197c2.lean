-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_specialize_det_lineForm_eq_a195f3e197c2
-- name    : P2M_GroundTheory_Heights__Heights_specialize_det_lineForm_eq_a195f3e197c2
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:50:04.344885+00:00
-- url     : https://prove2.me/theorems/f51dbb24-395b-4812-99f4-b4df7564748f
-- title:
--   P2 M Ground Theory Heights  Heights specialize det line Form eq a195f3e197c2: P2 M Ground Theory Heights  Heights specialize det line Form eq a195f3e197c2
-- statement:
--   The P2 M Ground Theory Heights  Heights specialize det line Form eq a195f3e197c2 construction uses the P2 M Ground Theory Heights  Heights specialize det line Form eq a195f3e197c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsSectionOrder.lean#L187-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsSectionOrder.lean#L187-L190

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

theorem P2M_GroundTheory_Heights__Heights_specialize_det_lineForm_eq_a195f3e197c2 :
    specFirst (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) tLine = -X (0, 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«specialize_det_lineForm_eq» := P2M_GroundTheory_Heights__Heights_specialize_det_lineForm_eq_a195f3e197c2
