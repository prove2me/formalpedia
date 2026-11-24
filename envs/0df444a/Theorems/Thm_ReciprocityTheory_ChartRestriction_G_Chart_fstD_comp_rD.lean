-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_fstD_comp_rD
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.fstD_comp_rD
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:35.176081+00:00
-- url     : https://prove2.me/theorems/bcf42665-72fe-453d-a2a7-974c1f329d6b
-- title:
--   Chart: fst D comp r D
-- statement:
--   The Chart construction uses the fst D comp r D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/RestrictDiagCompInclFst.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/RestrictDiagCompInclFst.lean#L72-L75

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.fstD_comp_rD (l : R × R →ₗ[R] R) : (fstD R).comp (rD l) = jetAug R (Fin 2) 1 := by sorry
