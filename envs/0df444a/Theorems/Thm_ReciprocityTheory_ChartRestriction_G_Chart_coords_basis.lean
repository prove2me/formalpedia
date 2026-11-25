-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_coords_basis
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.coords_basis
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:37.640638+00:00
-- url     : https://prove2.me/theorems/6946afd2-d01c-5122-b4a9-250f101d6cec
-- title:
--   Chart: coords basis
-- statement:
--   The Chart construction uses the coords basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/LiePush.lean#L221-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/LiePush.lean#L221-L235

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.coords_basis [IsLocalRing S] [Smooth G'.hom] {d n : ℕ} {v : Fin d → (epsR S ⟶ G')} {u : Fin n → (epsR S ⟶ G')}
    (hv : IsLieBasis v) (hu : IsLieBasis u) (U : Fin n → Fin d → S) (hU : ∀ i, IsLieComb (U i) v (u i)) (z : Fin d → S) :
    ∃! a : Fin n → S, ∀ j, ∑ i, a i * U i j = z j := by sorry
