-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_apra_blow
-- name    : ReciprocityTheory.L2DbarEstimates.Y.apra_blow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:01:26.109693+00:00
-- url     : https://prove2.me/theorems/589c5574-f327-56d0-9343-4a5f5cb55400
-- title:
--   Y: apra blow
-- statement:
--   The Y construction uses the apra blow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeA.lean#L68-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeA.lean#L68-L134

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Metric
open scoped ContDiff ENNReal
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.Y.apra_blow (d : ℕ) (hd : 1 ≤ d) (hMVI : MVIntStatement d) (ε : ℝ) (hε : 0 < ε) :
    ⨆ n : ℕ, ∫⁻ x : V d, apraW d ε (1 / ((n : ℝ) + 1)) ‖x‖ = ⊤ := by sorry
