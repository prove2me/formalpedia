-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_real_bound
-- name    : ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.real_bound
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:00:25.597131+00:00
-- url     : https://prove2.me/theorems/dee6cb40-ae8d-4950-ba39-75a176cc34dd
-- title:
--   Weighted Atlas: real bound
-- statement:
--   The Weighted Atlas construction uses the real bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ZLocLower.lean#L15-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ZLocLower.lean#L15-L60

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZLocLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.real_bound {d F Ssq Wsq C1 B2 c m6 : ℝ} {T n : ℕ} (hnT' : n < T) (hd : 0 ≤ d)
    (hF0 : 0 ≤ F) (hF : F ≤ (C1 * d ^ (T - n)) ^ 2 * B2) (hB2 : 0 ≤ B2) (hc : 0 < c)
    (hS : c * d ^ 2 ≤ Ssq) (hm : 0 < m6) (hW : m6 ≤ Wsq) :
    F * Ssq ^ (-((T : ℝ) - 1 / 2)) * Wsq ^ (-(1 / 2 : ℝ)) ≤
      (C1 ^ 2 * B2 * c ^ (-((T : ℝ) - 1 / 2)) * m6 ^ (-(1 / 2 : ℝ))) *
        d ^ (-2 * ((n : ℝ) - 1 / 2)) := by sorry
