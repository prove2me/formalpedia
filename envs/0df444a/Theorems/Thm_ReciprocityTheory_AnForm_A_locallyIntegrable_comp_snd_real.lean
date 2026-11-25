-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_locallyIntegrable_comp_snd_real
-- name    : ReciprocityTheory.AnForm.A.locallyIntegrable_comp_snd_real
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:06:15.606171+00:00
-- url     : https://prove2.me/theorems/da282a34-3730-4a41-804a-7abf6c888f40
-- title:
--   A: locally Integrable comp snd real
-- statement:
--   The A construction uses the locally Integrable comp snd real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LogInt.lean#L59-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LogInt.lean#L59-L73

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogIntSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A

theorem ReciprocityTheory.AnForm.A.locallyIntegrable_comp_snd_real {g : ℝ → ℝ} (hg : LocallyIntegrable g volume) :
    LocallyIntegrable (fun p : ℝ × ℝ => g p.2) volume := by sorry
