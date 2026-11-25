-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieBasis_iso
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.isLieBasis_iso
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:21:21.721749+00:00
-- url     : https://prove2.me/theorems/14202cd2-2fb7-47d1-af43-8db474b91cd6
-- title:
--   Chart: is Lie Basis iso
-- statement:
--   The Chart construction uses the is Lie Basis iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsLieBasisBaseChange.lean#L73-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsLieBasisBaseChange.lean#L73-L89

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.isLieBasis_iso {G' : Over (Spec (CommRingCat.of R))} [GrpObj G'] (e : G' ≅ G) [IsMonHom e.hom] {n : ℕ}
    {v : Fin n → (epsR R ⟶ G')} (hv : IsLieBasis fun i => v i ≫ e.hom) : IsLieBasis v := by sorry
