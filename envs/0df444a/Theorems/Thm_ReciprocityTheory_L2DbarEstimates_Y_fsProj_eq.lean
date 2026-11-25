-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fsProj_eq
-- name    : ReciprocityTheory.L2DbarEstimates.Y.fsProj_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:00:31.16666+00:00
-- url     : https://prove2.me/theorems/f8568306-6d4a-48f0-870f-3ac17b591542
-- title:
--   Y: fs Proj eq
-- statement:
--   The Y construction uses the fs Proj eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FourSum.lean#L17-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FourSum.lean#L17-L29

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourSum
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

theorem ReciprocityTheory.L2DbarEstimates.Y.fsProj_eq {f : ℕ} (s t : Fin f → ℝ) (h : fsProj f s = fsProj f t) :
    ∃ n : Fin f → ℤ, t = s + fun i => (n i : ℝ) := by sorry
