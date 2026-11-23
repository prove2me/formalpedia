-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fsFun_proj
-- name    : ReciprocityTheory.L2DbarEstimates.Y.fsFun_proj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:30:13.796769+00:00
-- url     : https://prove2.me/theorems/6d109d92-7c62-4f5c-a5c4-fc602235ccb4
-- title:
--   Y: fs Fun proj
-- statement:
--   The Y construction uses the fs Fun proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FourSum.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FourSum.lean#L34-L41

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

theorem ReciprocityTheory.L2DbarEstimates.Y.fsFun_proj {f : ℕ} (g : (Fin f → ℝ) → ℂ)
    (hper : ∀ x (n : Fin f → ℤ), g (x + fun i => (n i : ℝ)) = g x) (t : Fin f → ℝ) :
    fsFun g (fsProj f t) = g t := by sorry
