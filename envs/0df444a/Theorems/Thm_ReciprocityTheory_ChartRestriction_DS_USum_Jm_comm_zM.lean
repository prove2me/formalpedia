-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_Jm_comm_zM
-- name    : ReciprocityTheory.ChartRestriction.DS.USum.Jm_comm_zM
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:50:39.081172+00:00
-- url     : https://prove2.me/theorems/d6c88008-42ee-5270-9e83-c21552323754
-- title:
--   USum: Jm comm z M
-- statement:
--   The USum construction uses the Jm comm z M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/InKRealSmul.lean#L25-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/InKRealSmul.lean#L25-L41

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

theorem ReciprocityTheory.ChartRestriction.DS.USum.Jm_comm_zM {a b : Fin n} (hab : ε a = ε b) (c : ℂ) : Jm ε * zM a b c = zM a b c * Jm ε := by sorry
