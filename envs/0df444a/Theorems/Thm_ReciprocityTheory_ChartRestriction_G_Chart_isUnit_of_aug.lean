-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isUnit_of_aug
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.isUnit_of_aug
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:05.36493+00:00
-- url     : https://prove2.me/theorems/48c822fe-d333-43ce-a445-d48e0caed775
-- title:
--   Chart: is Unit of aug
-- statement:
--   The Chart construction uses the is Unit of aug property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/AlgChart.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/AlgChart.lean#L12-L14

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
import Definitions.Def_Lemmata_FirstBlockLemmaK_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_AlgChart
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
variable {R : Type} [CommRing R]

theorem ReciprocityTheory.ChartRestriction.G.Chart.isUnit_of_aug {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (hJ : IsNilpotent (RingHom.ker aug))
    (a : A) (ha : IsUnit (aug a)) : IsUnit a := by sorry
