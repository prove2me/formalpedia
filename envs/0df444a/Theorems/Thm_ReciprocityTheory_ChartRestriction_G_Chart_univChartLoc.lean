-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_univChartLoc
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:17.587921+00:00
-- url     : https://prove2.me/theorems/e35ce638-dbda-4998-b755-610df684b1b3
-- title:
--   Chart: univ Chart Loc
-- statement:
--   The Chart construction uses the univ Chart Loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/UnivChartLoc.lean#L100-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/UnivChartLoc.lean#L100-L221

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_AlgChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_IsUnivChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]

theorem ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [Smooth G.hom] :
    ∃ (d : ℕ) (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), IsUnivChart G d x := by sorry
