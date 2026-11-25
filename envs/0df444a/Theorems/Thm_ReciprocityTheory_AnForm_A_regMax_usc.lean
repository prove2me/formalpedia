-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_usc
-- name    : ReciprocityTheory.AnForm.A.regMax_usc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:19:40.221954+00:00
-- url     : https://prove2.me/theorems/9a655ee3-5619-408c-9256-8b5b616dc75e
-- title:
--   A: reg Max usc
-- statement:
--   The A construction uses the reg Max usc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L163-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L163-L175

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem ReciprocityTheory.AnForm.A.regMax_usc {X : Type*} [TopologicalSpace X] {U : Set X} (η : ℝ) {u : ι → X → ℝ}
    (hu : ∀ j, UpperSemicontinuousOn (u j) U) :
    UpperSemicontinuousOn (fun z => regMax η (fun j => u j z)) U := by sorry
