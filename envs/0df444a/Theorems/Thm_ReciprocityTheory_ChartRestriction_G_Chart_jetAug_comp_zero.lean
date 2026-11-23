-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_comp_zero
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.jetAug_comp_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:53.687349+00:00
-- url     : https://prove2.me/theorems/73888fc3-b18d-4844-a8e3-e65764067b21
-- title:
--   Chart: jet Aug comp zero
-- statement:
--   The Chart construction uses the jet Aug comp zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/AlgChart.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/AlgChart.lean#L33-L34

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.jetAug_comp_zero (n m : ℕ) : (jetAug R (Fin n) 0).comp (jetZeroR R (Fin n) m) = jetAug R (Fin n) m := by sorry
