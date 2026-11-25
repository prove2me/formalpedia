-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieBasis_baseChange
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.isLieBasis_baseChange
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:24:54.278611+00:00
-- url     : https://prove2.me/theorems/17a3acd0-8c30-4aad-80c9-dc7b0d936894
-- title:
--   Chart: is Lie Basis base Change
-- statement:
--   The Chart construction uses the is Lie Basis base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsLieBasisBaseChange.lean#L91-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsLieBasisBaseChange.lean#L91-L108

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
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
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem ReciprocityTheory.ChartRestriction.G.Chart.isLieBasis_baseChange [IsLocalRing R] [Smooth G.hom] {R' : Type} [CommRing R'] (f : R →+* R')
    {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G (Geo.Tor.spMap f) φ) {d : ℕ} {v : Fin d → (epsR R ⟶ G)} (hv : IsLieBasis v)
    {v' : Fin d → (epsR R' ⟶ G')} (hv' : ∀ j, (v' j).left ≫ φ = Geo.Tor.spMap (dualMapR f) ≫ (v j).left) :
    IsLieBasis v' := by sorry
