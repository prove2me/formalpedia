-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_chart_of_basis
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.chart_of_basis
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:26:01.178748+00:00
-- url     : https://prove2.me/theorems/30e6501b-57b9-4163-a116-800e8dc53a76
-- title:
--   Chart: chart of basis
-- statement:
--   The Chart construction uses the chart of basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsLieBasisBaseChange.lean#L15-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsLieBasisBaseChange.lean#L15-L49

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.chart_of_basis [IsLocalRing R] [Smooth G.hom] {d : ℕ} {v : Fin d → (epsR R ⟶ G)} (hv : IsLieBasis v) :
    ∃ x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G, IsUnivChart G d x ∧
      ∀ j, v j = spMap (dualLift (Pi.single j 1)) ≫ x 1 := by sorry
