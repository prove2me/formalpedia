-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_eq_comp
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.jetAug_eq_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:45:49.03919+00:00
-- url     : https://prove2.me/theorems/06dba45c-77c2-4a48-827b-c59225585a43
-- title:
--   Chart: jet Aug eq comp
-- statement:
--   The Chart construction uses the jet Aug eq comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/ChartLawPf.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/ChartLawPf.lean#L26-L27

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR epsScaleR IsTangent IsLieComb IsLieBasis)
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]

theorem ReciprocityTheory.ChartRestriction.G.Chart.jetAug_eq_comp (κ : Type) (m : ℕ) : jetAug R κ m = (jetAug R κ 0).comp (jetZeroR R κ m) := by sorry
