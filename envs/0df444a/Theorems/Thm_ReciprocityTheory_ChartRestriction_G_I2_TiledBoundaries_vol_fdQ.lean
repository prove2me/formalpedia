-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_vol_fdQ
-- name    : ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.vol_fdQ
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:43:36.81649+00:00
-- url     : https://prove2.me/theorems/938f941a-83c0-4b8b-a664-30ce6de84712
-- title:
--   Tiled Boundaries: vol fd Q
-- statement:
--   The Tiled Boundaries construction uses the vol fd Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/MemSpanMap.lean#L132-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/MemSpanMap.lean#L132-L138

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanBn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_TileIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory MeasureTheory.Measure Complex Module Set Submodule
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.vol_fdQ (X : PT E) {q : ℕ} (hq : 1 ≤ q) : volume.real (ZSpan.fundamentalDomain (bQ X hq)) =
    (((q : ℝ) ^ Fintype.card (Idx X.dim)) ^ 2)⁻¹ * volume.real (ZSpan.fundamentalDomain X.b) := by sorry
