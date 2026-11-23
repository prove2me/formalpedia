-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_comp_trunc
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.jetAug_comp_trunc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:52.112524+00:00
-- url     : https://prove2.me/theorems/0530bfbc-4e9a-4e49-8e69-1a391009dbb2
-- title:
--   Chart: jet Aug comp trunc
-- statement:
--   The Chart construction uses the jet Aug comp trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/AlgChart.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/AlgChart.lean#L30-L31

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.jetAug_comp_trunc (n m : ℕ) : (jetAug R (Fin n) m).comp (jetTruncR R (Fin n) m) = jetAug R (Fin n) (m + 1) := by sorry
