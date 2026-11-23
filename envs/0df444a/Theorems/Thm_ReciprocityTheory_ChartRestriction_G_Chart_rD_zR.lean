-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rD_zR
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.rD_zR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:37.198903+00:00
-- url     : https://prove2.me/theorems/06250b8e-4846-42c2-8a3f-fff5091b3264
-- title:
--   Chart: r D z R
-- statement:
--   The Chart construction uses the r D z R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/RestrictDiagCompInclFst.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/RestrictDiagCompInclFst.lean#L63-L65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_RestrictDiagCompInclFst
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

theorem ReciprocityTheory.ChartRestriction.G.Chart.rD_zR (l : R × R →ₗ[R] R) (i : Fin 2) :
    rD l (zR 1 i) = TrivSqZeroExt.inr (l (if i = 0 then ((1 : R), (0 : R)) else (0, 1))) := by sorry
