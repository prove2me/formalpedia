-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_fderiv2_nonneg
-- name    : ReciprocityTheory.AnForm.A.regMax_fderiv2_nonneg
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:19:32.502402+00:00
-- url     : https://prove2.me/theorems/bcef33d8-f5e4-4a22-ae68-881eb2f9b48a
-- title:
--   A: reg Max fderiv2 nonneg
-- statement:
--   The A construction uses the reg Max fderiv2 nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L291-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L291-L318

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem ReciprocityTheory.AnForm.A.regMax_fderiv2_nonneg {η : ℝ} (hη : 0 < η) (p a : ι → ℝ) :
    0 ≤ fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) p a a := by sorry
