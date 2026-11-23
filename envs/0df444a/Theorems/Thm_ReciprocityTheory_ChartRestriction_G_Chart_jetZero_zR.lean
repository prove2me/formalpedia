-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetZero_zR
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.jetZero_zR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:53.258998+00:00
-- url     : https://prove2.me/theorems/fba7bca1-7111-4fa3-a384-40f9cd1cb067
-- title:
--   Chart: jet Zero z R
-- statement:
--   The Chart construction uses the jet Zero z R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/AlgChart.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/AlgChart.lean#L36-L39

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.jetZero_zR (n m : ℕ) (j : Fin n) : jetZeroR R (Fin n) m (zR m j) = 0 := by sorry
