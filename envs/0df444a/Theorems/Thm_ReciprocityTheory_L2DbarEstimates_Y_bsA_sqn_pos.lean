-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_sqn_pos
-- name    : ReciprocityTheory.L2DbarEstimates.Y.bsA_sqn_pos
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:18:07.704405+00:00
-- url     : https://prove2.me/theorems/4f5cb152-38bc-57ea-b124-07744fe35dfa
-- title:
--   Y: bs A sqn pos
-- statement:
--   The Y construction uses the bs A sqn pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepA.lean#L148-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepA.lean#L148-L152

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
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
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem ReciprocityTheory.L2DbarEstimates.Y.bsA_sqn_pos {la : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {y : Y}
    (h : ∃ k, w k (A.pick y) y ≠ 0) : 0 < A.sqn la w y := by sorry
