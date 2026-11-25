-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_scale
-- name    : ReciprocityTheory.AnForm.A.regMax_scale
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:20:24.072776+00:00
-- url     : https://prove2.me/theorems/4fc77d35-536f-517e-b9b9-055bed4b197a
-- title:
--   A: reg Max scale
-- statement:
--   The A construction uses the reg Max scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L324-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L324-L331

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

theorem ReciprocityTheory.AnForm.A.regMax_scale {η : ℝ} (hη : 0 < η) (t : ι → ℝ) : regMax η t = η * regMax 1 (η⁻¹ • t) := by sorry
