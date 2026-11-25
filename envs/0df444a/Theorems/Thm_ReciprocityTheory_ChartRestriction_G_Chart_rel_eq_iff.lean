-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_eq_iff
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.rel_eq_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:16:59.517942+00:00
-- url     : https://prove2.me/theorems/092fcf9b-61ee-5154-bd43-b047ba411c96
-- title:
--   Chart: rel eq iff
-- statement:
--   The Chart construction uses the rel eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankPf.lean#L58-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankPf.lean#L58-L64

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.rel_eq_iff {X : Over (Spec (CommRingCat.of k))} {w₁ w₂ : viaT tk X ⟶ G'} {v₁ v₂ : X ⟶ (Over.pullback g).obj G}
    (h₁ : Rel (F := F) tk g w₁ v₁) (h₂ : Rel (F := F) tk g w₂ v₂) : w₁ = w₂ ↔ v₁ = v₂ := by sorry
