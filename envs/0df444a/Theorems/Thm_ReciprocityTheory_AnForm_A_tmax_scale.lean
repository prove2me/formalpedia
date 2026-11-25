-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_scale
-- name    : ReciprocityTheory.AnForm.A.tmax_scale
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:19:19.14392+00:00
-- url     : https://prove2.me/theorems/9e7e73a2-a66c-41e8-943e-d26ce336c619
-- title:
--   A: tmax scale
-- statement:
--   The A construction uses the tmax scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L315-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L315-L322

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

theorem ReciprocityTheory.AnForm.A.tmax_scale {η : ℝ} (hη : 0 < η) (t h : ι → ℝ) :
    tmax (fun j => t j + η * h j) = η * tmax (fun j => (η⁻¹ • t) j + 1 * h j) := by sorry
