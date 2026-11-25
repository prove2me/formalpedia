-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_dAway_eps
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.dAway_eps
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:27:03.461382+00:00
-- url     : https://prove2.me/theorems/a786d3a4-4960-5c17-9d70-f29f0ba0f7af
-- title:
--   Chart: d Away eps
-- statement:
--   The Chart construction uses the d Away eps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSOfIdToRingHom.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSOfIdToRingHom.lean#L24-L25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanSRestrict
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] (s : S)

theorem ReciprocityTheory.ChartRestriction.G.Chart.dAway_eps : dAway s (TrivSqZeroExt.inr 1) = TrivSqZeroExt.inr 1 := by sorry
