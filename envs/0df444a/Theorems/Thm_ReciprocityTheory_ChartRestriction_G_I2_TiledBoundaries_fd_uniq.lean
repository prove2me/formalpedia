-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_fd_uniq
-- name    : ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.fd_uniq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:06.949026+00:00
-- url     : https://prove2.me/theorems/60c0a03a-555c-42ff-9b8c-ab86318d3e05
-- title:
--   Tiled Boundaries: fd uniq
-- statement:
--   The Tiled Boundaries construction uses the fd uniq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/TileIntegral.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/TileIntegral.lean#L23-L28

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

theorem ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.fd_uniq (b : Basis ι ℝ V) {x β1 β2 : V} (h1 : β1 ∈ span ℤ (range b))
    (h2 : β2 ∈ span ℤ (range b)) (hx1 : β1 + x ∈ ZSpan.fundamentalDomain b)
    (hx2 : β2 + x ∈ ZSpan.fundamentalDomain b) : β1 = β2 := by sorry
