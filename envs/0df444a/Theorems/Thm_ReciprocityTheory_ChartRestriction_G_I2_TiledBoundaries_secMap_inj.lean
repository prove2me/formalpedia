-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_secMap_inj
-- name    : ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.secMap_inj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:15:23.982896+00:00
-- url     : https://prove2.me/theorems/5d67b444-88d2-4354-b4bf-35596523f0a2
-- title:
--   Tiled Boundaries: sec Map inj
-- statement:
--   The Tiled Boundaries construction uses the sec Map inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/ETSymmApply.lean#L130-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/ETSymmApply.lean#L130-L135

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanBn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_ETSymmApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex Module
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.secMap_inj (X : PT E) (q n : ℕ) : Function.Injective (secMap X q n) := by sorry
