-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_mem_reps
-- name    : ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.mem_reps
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:30.574024+00:00
-- url     : https://prove2.me/theorems/d50d97e5-0636-4651-a74a-99b3de12af94
-- title:
--   Tiled Boundaries: mem reps
-- statement:
--   The Tiled Boundaries construction uses the mem reps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/TileIntegral.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/TileIntegral.lean#L17-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_TileIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open MeasureTheory Module Set Submodule
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.mem_reps {bA bB : Basis ι ℝ V} {c : V} :
    c ∈ reps bA bB ↔ c ∈ ZSpan.fundamentalDomain bA ∧ c ∈ span ℤ (range bB) := by sorry
