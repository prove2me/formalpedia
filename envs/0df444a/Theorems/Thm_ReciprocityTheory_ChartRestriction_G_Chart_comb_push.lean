-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_comb_push
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.comb_push
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:32:36.506212+00:00
-- url     : https://prove2.me/theorems/00b09370-ecbd-4d15-ba90-401921d12a13
-- title:
--   Chart: comb push
-- statement:
--   The Chart construction uses the comb push property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/LiePush.lean#L83-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/LiePush.lean#L83-L102

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LiePush
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp
open scoped CategoryTheory.Obj
variable {S : Type} [CommRing S] {X : Scheme.{0}} {x : Sp S ⟶ X} {G : Over X} {G' : Over (Sp S)} [GrpObj G] [GrpObj G']
  {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ)
include h

theorem ReciprocityTheory.ChartRestriction.G.Chart.comb_push {n : ℕ} (c : Fin n → S) (v : Fin n → (epsR S ⟶ G')) (w : epsR S ⟶ G') : IsLieComb c v w ↔
    ∃ u : Fin n → (Over.mk (Geo.Tor.spMap (algebraMap S (DualNumber S)) ≫ x) ⟶ G),
      (∀ i, (u i).left = Geo.Tor.spMap (epsScaleR (c i)) ≫ (v i).left ≫ φ) ∧ (List.ofFn u).prod.left = w.left ≫ φ := by sorry
