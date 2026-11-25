-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogLogRegularisation_le_glue_6f79181c8cf1
-- name    : P2M_GroundTheory_Heights__Heights_Regular_LogLogRegularisation_le_glue_6f79181c8cf1
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:56:27.443163+00:00
-- url     : https://prove2.me/theorems/2d25b7e2-adfa-4b70-a867-67eb7e86835c
-- title:
--   P2 M Ground Theory Heights  Heights Regular Log Log Regularisation le glue 6f79181c8cf1: P2 M Ground Theory Heights  Heights Regular Log Log Regularisation le glue 6f79181c8cf1
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Log Log Regularisation le glue 6f79181c8cf1 construction uses the P2 M Ground Theory Heights  Heights Regular Log Log Regularisation le glue 6f79181c8cf1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ChartFun.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ChartFun.lean#L20-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsChartBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ChartFun
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_tmax
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_ge
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_le
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_le

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
open Metric Filter Topology
open ReciprocityTheory.AnForm.A (Mollifier tmax regMax le_tmax tmax_le regMax_ge regMax_le)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.LogLogRegularisation
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X}
open Classical

theorem P2M_GroundTheory_Heights__Heights_Regular_LogLogRegularisation_le_glue_6f79181c8cf1 (P : PotentialCharts A) (a : Fin P.N → X → ℝ) {ε : ℝ} (hε : 0 ≤ ε) {x : X}
    {j : Fin P.N} (hx : x ∈ P.mid j) : a j x ≤ P.glue a ε x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«LogLogRegularisation».«le_glue» := P2M_GroundTheory_Heights__Heights_Regular_LogLogRegularisation_le_glue_6f79181c8cf1
