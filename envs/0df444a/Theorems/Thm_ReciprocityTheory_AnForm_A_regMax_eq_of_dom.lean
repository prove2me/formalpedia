-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_eq_of_dom
-- name    : ReciprocityTheory.AnForm.A.regMax_eq_of_dom
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:19:35.925111+00:00
-- url     : https://prove2.me/theorems/800c35e9-bc96-42c7-aa82-e156572409c5
-- title:
--   A: reg Max eq of dom
-- statement:
--   The A construction uses the reg Max eq of dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L230-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L230-L243

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
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

theorem ReciprocityTheory.AnForm.A.regMax_eq_of_dom {η : ℝ} (hη : 0 ≤ η) (t : ι → ℝ) (i : ι)
    (hi : ∀ j, j ≠ i → t j + η ≤ t i) : regMax η t = t i := by sorry
