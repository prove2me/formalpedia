-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartChoice_specFirst_zero_of_isMultiHomog_3496bbd45abd
-- name    : P2M_GroundTheory_Heights__Heights_ChartChoice_specFirst_zero_of_isMultiHomog_3496bbd45abd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:17:41.685204+00:00
-- url     : https://prove2.me/theorems/f504a40a-17a6-4026-9ea7-dea46765bdbd
-- title:
--   P2 M Ground Theory Heights  Heights Chart Choice spec First zero of is Multi Homog 3496bbd45abd: P2 M Ground Theory Heights  Heights Chart Choice spec First zero of is Multi Homog 3496bbd45abd
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Choice spec First zero of is Multi Homog 3496bbd45abd construction uses the P2 M Ground Theory Heights  Heights Chart Choice spec First zero of is Multi Homog 3496bbd45abd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartChoice.lean#L51-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartChoice.lean#L51-L72

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

theorem P2M_GroundTheory_Heights__Heights_ChartChoice_specFirst_zero_of_isMultiHomog_3496bbd45abd {δ : ℕ} (hδ : 1 ≤ δ) {f : MvPolynomial (Fin (e + 1) × Fin n) F}
    (hf : IsMultiHomog δ f) : specFirst f 0 = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartChoice».«specFirst_zero_of_isMultiHomog» := P2M_GroundTheory_Heights__Heights_ChartChoice_specFirst_zero_of_isMultiHomog_3496bbd45abd
