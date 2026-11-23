-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_elt_nil
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.elt_nil
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:47.558253+00:00
-- url     : https://prove2.me/theorems/d44d03dc-a4f3-4673-a35a-d3467fa972e6
-- title:
--   Chart: elt nil
-- statement:
--   The Chart construction uses the elt nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/AlgChart.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/AlgChart.lean#L19-L25

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.elt_nil {A : Type} [CommRing A] (J : Ideal A) (hJ : IsNilpotent J) : ∀ a ∈ J, IsNilpotent a := by sorry
