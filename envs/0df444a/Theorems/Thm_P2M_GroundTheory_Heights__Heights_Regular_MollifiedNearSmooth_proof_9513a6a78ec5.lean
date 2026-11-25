-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_MollifiedNearSmooth_proof_9513a6a78ec5
-- name    : P2M_GroundTheory_Heights__Heights_Regular_MollifiedNearSmooth_proof_9513a6a78ec5
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:46:22.384501+00:00
-- url     : https://prove2.me/theorems/3ec82c8e-05f8-5cb6-aaa2-257e795676c6
-- title:
--   P2 M Ground Theory Heights  Heights Regular Mollified Near Smooth proof 9513a6a78ec5: P2 M Ground Theory Heights  Heights Regular Mollified Near Smooth proof 9513a6a78ec5
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Mollified Near Smooth proof 9513a6a78ec5 construction uses the P2 M Ground Theory Heights  Heights Regular Mollified Near Smooth proof 9513a6a78ec5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PMollifiedNearSmooth.lean#L134-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PMollifiedNearSmooth.lean#L134-L257

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartComparison
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PMollifiedNearSmooth
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ChartComparison_proof_cb37c5d74969
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_le__638c0d78514a
import Theorems.Thm_ReciprocityTheory_AnForm_A_mollify_thm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric
open scoped ContDiff
open ReciprocityTheory.AnForm.A (polyMax molli mollify_thm polyMax_le' coordDiv limsupExt)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_MollifiedNearSmooth_proof_9513a6a78ec5 (h : TruncPsh.Statement) : MollifiedNearSmooth.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«MollifiedNearSmooth».«proof» := P2M_GroundTheory_Heights__Heights_Regular_MollifiedNearSmooth_proof_9513a6a78ec5
