-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_SimpleNormalCrossingSliceCharts_analyticAt_removeNth_comp
-- name    : ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.analyticAt_removeNth_comp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:19:27.151107+00:00
-- url     : https://prove2.me/theorems/6a7eb19c-d2b8-5438-b806-f4517c79f999
-- title:
--   Simple Normal Crossing Slice Charts: analytic At remove Nth comp
-- statement:
--   The Simple Normal Crossing Slice Charts construction uses the analytic At remove Nth comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/SNCAtlas.lean#L134-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/SNCAtlas.lean#L134-L139

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_SNCAtlas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Topology Filter Set
open scoped ContDiff
noncomputable section
open ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts
variable {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.analyticAt_removeNth_comp {e : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (i : Fin (e + 1)) {F : E → Fin (e + 1) → ℂ} {z : E} (hF : AnalyticAt ℂ F z) :
    AnalyticAt ℂ (fun z' => i.removeNth (F z')) z := by sorry
