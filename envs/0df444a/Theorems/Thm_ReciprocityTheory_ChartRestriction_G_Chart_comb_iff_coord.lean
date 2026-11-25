-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_comb_iff_coord
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.comb_iff_coord
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:38:07.837841+00:00
-- url     : https://prove2.me/theorems/cac1c12b-d824-51a5-9129-572c04872f2d
-- title:
--   Chart: comb iff coord
-- statement:
--   The Chart construction uses the comb iff coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/LiePush.lean#L162-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/LiePush.lean#L162-L167

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.comb_iff_coord {n d : ℕ} {y : ∀ m : ℕ, sp (R₀ := S) (JetR S (Fin n) m) ⟶ G'} (hy : IsUnivChart G' n y) (c : Fin d → S)
    {v : Fin d → (epsR S ⟶ G')} (hv : ∀ i, IsTan (v i)) {w : epsR S ⟶ G'} (hw : IsTan w) :
    IsLieComb c v w ↔ tcoord hy w hw = ∑ i, c i • tcoord hy (v i) (hv i) := by sorry
