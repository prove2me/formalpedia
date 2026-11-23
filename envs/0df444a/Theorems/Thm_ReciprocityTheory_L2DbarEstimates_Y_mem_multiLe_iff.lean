-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_mem_multiLe_iff
-- name    : ReciprocityTheory.L2DbarEstimates.Y.mem_multiLe_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:32:47.719576+00:00
-- url     : https://prove2.me/theorems/fcd24644-6129-45de-b29f-554d776ee7cb
-- title:
--   Y: mem multi Le iff
-- statement:
--   The Y construction uses the mem multi Le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/IndCount.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/IndCount.lean#L14-L23

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IndCount
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
universe u
open Finset

theorem ReciprocityTheory.L2DbarEstimates.Y.mem_multiLe_iff {n j : ℕ} {α : Fin n → ℕ} : α ∈ multiLe n j ↔ ∑ i, α i ≤ j := by sorry
