-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_chart_away
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.chart_away
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:25:20.062876+00:00
-- url     : https://prove2.me/theorems/9b436619-8177-4cc7-bc36-db317554e8c6
-- title:
--   Chart: chart away
-- statement:
--   The Chart construction uses the chart away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ChartAway.lean#L22-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ChartAway.lean#L22-L54

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ChartAway
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
variable {S : Type} [CommRing S] (G : Over (Spec (CommRingCat.of S))) [GrpObj G]
set_option backward.isDefEq.respectTransparency.types false

theorem ReciprocityTheory.ChartRestriction.G.Chart.chart_away (U : G.left.Opens) (hU : IsAffineOpen U) (s : S)
    (hs : ∀ x : Spec (CommRingCat.of S), s ∉ x.asIdeal → (η[G]).left x ∈ U) : Nonempty (Chart (Gs G s)) := by sorry
