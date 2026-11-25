-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartChoice_joinFirst_C_58f1c58d3e33
-- name    : P2M_GroundTheory_Heights__Heights_ChartChoice_joinFirst_C_58f1c58d3e33
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:17:16.404198+00:00
-- url     : https://prove2.me/theorems/f039cd82-61ac-459a-8c12-0e7ce098e1a9
-- title:
--   P2 M Ground Theory Heights  Heights Chart Choice join First C 58f1c58d3e33: P2 M Ground Theory Heights  Heights Chart Choice join First C 58f1c58d3e33
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Choice join First C 58f1c58d3e33 construction uses the P2 M Ground Theory Heights  Heights Chart Choice join First C 58f1c58d3e33 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartChoice.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartChoice.lean#L37-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartChoice
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
open GroundTheory.Heights₂.Heights.ChartChoice
variable {F : Type} [Field F] {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartChoice_joinFirst_C_58f1c58d3e33 (a : MvPolynomial (Fin e × Fin n) F) :
    joinFirst F e n (C a) = rename (shiftVar e n) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartChoice».«joinFirst_C» := P2M_GroundTheory_Heights__Heights_ChartChoice_joinFirst_C_58f1c58d3e33
