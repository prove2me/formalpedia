-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_fderiv_regMax
-- name    : ReciprocityTheory.AnForm.A.fderiv_regMax
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:47.855437+00:00
-- url     : https://prove2.me/theorems/32a05c55-53cc-4452-a9e9-d2fe2e8fe54c
-- title:
--   A: fderiv reg Max
-- statement:
--   The A construction uses the fderiv reg Max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L106-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L106-L113

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

theorem ReciprocityTheory.AnForm.A.fderiv_regMax {η : ℝ} (hη : 0 < η) :
    fderiv ℝ (regMax (ι := ι) η) = fun t => fderiv ℝ (regMax (ι := ι) 1) (η⁻¹ • t) := by sorry
