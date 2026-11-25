-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_eq_of_comb_single
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.eq_of_comb_single
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:59:51.732084+00:00
-- url     : https://prove2.me/theorems/53a373df-fbd3-558c-abe5-58f1cf475dac
-- title:
--   Chart: eq of comb single
-- statement:
--   The Chart construction uses the eq of comb single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/LiePush.lean#L170-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/LiePush.lean#L170-L218

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.eq_of_comb_single [IsLocalRing S] [Smooth G'.hom] {d : ℕ} {v : Fin d → (epsR S ⟶ G')} (hv : ∀ i, IsTangent (v i))
    {w : epsR S ⟶ G'} (hw : IsTangent w) (j : Fin d) (hc : IsLieComb (Pi.single j 1) v w) : w = v j := by sorry
