-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_eig_iff
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.eig_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:16.030787+00:00
-- url     : https://prove2.me/theorems/771d2d18-c9a4-4fdc-a28c-9e18633d09e7
-- title:
--   Chart: eig iff
-- statement:
--   The Chart construction uses the eig iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankPf.lean#L89-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankPf.lean#L89-L98

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : Geo.Tor.IsGrpPullback G' G f F) {k : Type} [Field k] {tk : Spec (CommRingCat.of k) ⟶ S'}
  {g : Spec (CommRingCat.of k) ⟶ S} (hg : tk ≫ f = g)
include hc

theorem ReciprocityTheory.ChartRestriction.G.Chart.eig_iff (a : G' ⟶ G') (b : G ⟶ G) (hab : a.left ≫ F = F ≫ b.left) (s : k)
    {w : viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G'} {v : sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) :
    (w ≫ a).left = Geo.Tor.spMap (Geo.Tor.epsScale s) ≫ w.left ↔ v ≫ (Over.pullback g).map b = spMap (scaleD s) ≫ v := by sorry
