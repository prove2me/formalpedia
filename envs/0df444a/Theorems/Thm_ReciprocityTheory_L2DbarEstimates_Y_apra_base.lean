-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_apra_base
-- name    : ReciprocityTheory.L2DbarEstimates.Y.apra_base
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:00:52.1847+00:00
-- url     : https://prove2.me/theorems/4f2b77de-dfbc-4771-b356-a072200bdf8c
-- title:
--   Y: apra base
-- statement:
--   The Y construction uses the apra base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeA.lean#L47-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeA.lean#L47-L66

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

theorem ReciprocityTheory.L2DbarEstimates.Y.apra_base (k : ℕ) (hMVk : MVStatement k) (ε : ℝ) (g : V k → ℂ)
    (hg : DifferentiableOn ℂ g (ball 0 ε)) :
    ENNReal.ofReal (‖g 0‖ ^ 2) * volume (ball (0 : V k) ε) ≤
      ∫⁻ ζ in ball (0 : V k) ε, ENNReal.ofReal (‖g ζ‖ ^ 2) := by sorry
