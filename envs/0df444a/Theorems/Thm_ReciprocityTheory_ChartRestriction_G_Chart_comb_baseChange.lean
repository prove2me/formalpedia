-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_comb_baseChange
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.comb_baseChange
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:44:16.616382+00:00
-- url     : https://prove2.me/theorems/6767b16a-7b75-420d-8ae2-1da659a0a434
-- title:
--   Chart: comb base Change
-- statement:
--   The Chart construction uses the comb base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/LiePush.lean#L105-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/LiePush.lean#L105-L159

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LiePush
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
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
omit h

theorem ReciprocityTheory.ChartRestriction.G.Chart.comb_baseChange {R : Type} [CommRing R] {G₀ : Over (Sp R)} [GrpObj G₀] (f : R →+* S) {ψ : G'.left ⟶ G₀.left}
    (h : IsGrpPullback G' G₀ (Geo.Tor.spMap f) ψ) {n : ℕ} {c : Fin n → R} {v : Fin n → (epsR R ⟶ G₀)} {w : epsR R ⟶ G₀}
    (hc : IsLieComb c v w) {v' : Fin n → (epsR S ⟶ G')} {w' : epsR S ⟶ G'}
    (hv : ∀ i, (v' i).left ≫ ψ = Geo.Tor.spMap (dualMapR f) ≫ (v i).left)
    (hw : w'.left ≫ ψ = Geo.Tor.spMap (dualMapR f) ≫ w.left) : IsLieComb (fun i => f (c i)) v' w' := by sorry
