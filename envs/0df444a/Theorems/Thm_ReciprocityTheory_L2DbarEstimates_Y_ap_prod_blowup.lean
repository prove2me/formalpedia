-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ap_prod_blowup
-- name    : ReciprocityTheory.L2DbarEstimates.Y.ap_prod_blowup
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:06:53.105831+00:00
-- url     : https://prove2.me/theorems/5f013963-6ac6-4581-9907-236049b27cd7
-- title:
--   Y: ap prod blowup
-- statement:
--   The Y construction uses the ap prod blowup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeA.lean#L136-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeA.lean#L136-L190

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

theorem ReciprocityTheory.L2DbarEstimates.Y.ap_prod_blowup (d k : ℕ) (hd : 1 ≤ d) (hMVd : MVStatement d) (hMVk : MVStatement k)
    (hMVI : MVIntStatement d) (ε : ℝ) (hε : 0 < ε) (M : ℝ) :
    ∃ τ0 : ℝ, 0 < τ0 ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ0 → ∀ u : V d × V k → ℂ,
      DifferentiableOn ℂ u (Metric.ball (0 : V d) ε ×ˢ Metric.ball (0 : V k) ε) →
      ENNReal.ofReal (M * ‖u 0‖ ^ 2) ≤
        ∫⁻ z in Metric.ball (0 : V d) ε ×ˢ Metric.ball (0 : V k) ε,
          ENNReal.ofReal (‖u z‖ ^ 2 * (max (‖z.1‖ ^ 2) τ) ^ (-(d : ℝ))) := by sorry
