-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isGrpPullback_factor
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:17:55.757915+00:00
-- url     : https://prove2.me/theorems/e8494ea8-d6c1-468a-8785-0d960789c1f7
-- title:
--   Chart: is Grp Pullback factor
-- statement:
--   The Chart construction uses the is Grp Pullback factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsGrpPullbackFactor.lean#L63-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsGrpPullbackFactor.lean#L63-L105

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsAwayNotMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullbackFactor
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

theorem ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor {S S' S'' : Scheme.{0}} {G : Over S} [GrpObj G] {G'' : Over S''} [GrpObj G'']
    (f : S' ⟶ S) (g : S'' ⟶ S') {F : G''.left ⟶ G.left} (h : Geo.Tor.IsGrpPullback G'' G (g ≫ f) F) :
    Geo.Tor.IsGrpPullback G'' ((Over.pullback f).obj G) g
      (pullback.lift F (G''.hom ≫ g) (by rw [h.1.w, Category.assoc])) := by sorry
