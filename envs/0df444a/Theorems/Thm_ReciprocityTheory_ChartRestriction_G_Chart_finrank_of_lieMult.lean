-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_finrank_of_lieMult
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.finrank_of_lieMult
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:09:40.458543+00:00
-- url     : https://prove2.me/theorems/a6c017ea-bc92-460a-9c64-e6f3b9f49013
-- title:
--   Chart: finrank of lie Mult
-- statement:
--   The Chart construction uses the finrank of lie Mult property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankPf.lean#L108-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankPf.lean#L108-L173

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
variable {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := k) (JetR k (Fin n) m) ⟶ (Over.pullback g).obj G} (hx : IsUnivChart _ n x)
  {O : Type} [CommRing O] (act : Geo.Tor.OAct O G') (b : O → (G ⟶ G))
  (hab : ∀ a, (act.act a).left ≫ F = F ≫ (b a).left)
  (act' : O → ((Over.pullback g).obj G ⟶ (Over.pullback g).obj G)) [∀ a, IsMonHom (act' a)]
  (hact' : ∀ a, act' a = (Over.pullback g).map (b a)) (τ : O →+* k)
include hc hg hab hact'

theorem ReciprocityTheory.ChartRestriction.G.Chart.finrank_of_lieMult {N : ℕ} (hL : Geo.Tor.LieMult act tk τ N) :
    Module.finrank k (eigLat hx act' (fun a => τ a)) = N := by sorry
