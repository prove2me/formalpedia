-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_SimpleNormalCrossingSliceCharts_analyticAt_ins
-- name    : ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.analyticAt_ins
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:55.841343+00:00
-- url     : https://prove2.me/theorems/b18cdc14-92f0-4aa9-9361-f12ac040bc9b
-- title:
--   Simple Normal Crossing Slice Charts: analytic At ins
-- statement:
--   The Simple Normal Crossing Slice Charts construction uses the analytic At ins property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/SNCAtlas.lean#L122-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/SNCAtlas.lean#L122-L132

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

theorem ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.analyticAt_ins {e : ℕ} (i : Fin (e + 1)) (z : Fin e → ℂ) :
    AnalyticAt ℂ (fun z' : Fin e → ℂ => Fin.insertNth (α := fun _ => ℂ) i 0 z') z := by sorry
