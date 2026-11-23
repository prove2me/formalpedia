-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_locallyIntegrable_comp_eval_fin
-- name    : ReciprocityTheory.AnForm.A.locallyIntegrable_comp_eval_fin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:45.125473+00:00
-- url     : https://prove2.me/theorems/ededf94a-29b9-49c2-85f0-6614ba4c96d9
-- title:
--   A: locally Integrable comp eval fin
-- statement:
--   The A construction uses the locally Integrable comp eval fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LogInt.lean#L7-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LogInt.lean#L7-L41

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

theorem ReciprocityTheory.AnForm.A.locallyIntegrable_comp_eval_fin {D : ℕ} (i : Fin D) {g : ℂ → ℝ}
    (hg : LocallyIntegrable g volume) :
    LocallyIntegrable (fun z : Fin D → ℂ => g (z i)) volume := by sorry
