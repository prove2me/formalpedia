-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_bdd_trans
-- name    : ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.bdd_trans
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:27:38.937748+00:00
-- url     : https://prove2.me/theorems/aa57ad95-96e0-5570-b14b-e46ec769c0a4
-- title:
--   Tiled Boundaries: bdd trans
-- statement:
--   The Tiled Boundaries construction uses the bdd trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/TileIntegral.lean#L107-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/TileIntegral.lean#L107-L114

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

theorem ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.bdd_trans {s : Set V} (hs : Bornology.IsBounded s) (c : V) :
    Bornology.IsBounded ((fun x => x - c) ⁻¹' s) := by sorry
