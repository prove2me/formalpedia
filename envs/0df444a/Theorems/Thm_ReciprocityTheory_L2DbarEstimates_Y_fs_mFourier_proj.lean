-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fs_mFourier_proj
-- name    : ReciprocityTheory.L2DbarEstimates.Y.fs_mFourier_proj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:32:43.760231+00:00
-- url     : https://prove2.me/theorems/20515385-86fe-4b42-8edc-59726389cb7e
-- title:
--   Y: fs m Fourier proj
-- statement:
--   The Y construction uses the fs m Fourier proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FourSum.lean#L50-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FourSum.lean#L50-L59

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

theorem ReciprocityTheory.L2DbarEstimates.Y.fs_mFourier_proj {f : ℕ} (m : Fin f → ℤ) (t : Fin f → ℝ) :
    UnitAddTorus.mFourier m (fsProj f t) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ k, (m k : ℂ) * (t k : ℂ)) := by sorry
