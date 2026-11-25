-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_eq_of_forall_le
-- name    : ReciprocityTheory.AnForm.A.tmax_eq_of_forall_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:19:36.539034+00:00
-- url     : https://prove2.me/theorems/4c8094cb-6289-463c-81e8-b0df28700ce2
-- title:
--   A: tmax eq of forall le
-- statement:
--   The A construction uses the tmax eq of forall le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L32-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L32-L32

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

theorem ReciprocityTheory.AnForm.A.tmax_eq_of_forall_le {t : ι → ℝ} {i : ι} (h : ∀ j, t j ≤ t i) : tmax t = t i := by sorry
