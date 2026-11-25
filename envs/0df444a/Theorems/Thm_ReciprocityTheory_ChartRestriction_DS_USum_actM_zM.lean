-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_actM_zM
-- name    : ReciprocityTheory.ChartRestriction.DS.USum.actM_zM
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:46:08.34081+00:00
-- url     : https://prove2.me/theorems/0f151e00-a1eb-4b56-855c-751ec3a37685
-- title:
--   USum: act M z M
-- statement:
--   The USum construction uses the act M z M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/InKRealSmul.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/InKRealSmul.lean#L80-L83

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_InKRealSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
open ReciprocityTheory.ChartRestriction.DS.USum
variable {n : ℕ} {ε : Fin n → Bool}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.USum.actM_zM (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (c : ℂ) :
    actM E (zM a b c) = c • E a b - star c • E b a := by sorry
