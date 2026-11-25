-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_away_ext
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.away_ext
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:33:34.913883+00:00
-- url     : https://prove2.me/theorems/5a643182-d2f2-4c45-844b-1b3141b51512
-- title:
--   Chart: away ext
-- statement:
--   The Chart construction uses the away ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PairCompat.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PairCompat.lean#L14-L20

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ScalePowMono
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PairCompat
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

theorem ReciprocityTheory.ChartRestriction.G.Chart.away_ext {S : Type} [CommRing S] (u : S) {B : Type} [CommRing B] [Algebra S B]
    (f g : Localization.Away u →ₐ[S] B) : f = g := by sorry
