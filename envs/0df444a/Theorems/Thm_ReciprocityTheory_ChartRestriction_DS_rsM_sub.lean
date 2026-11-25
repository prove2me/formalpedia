-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rsM_sub
-- name    : ReciprocityTheory.ChartRestriction.DS.rsM_sub
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:53:41.598295+00:00
-- url     : https://prove2.me/theorems/388fa5a2-6f55-4d32-b88c-b5871af9ec95
-- title:
--   DS: rs M sub
-- statement:
--   The DS construction uses the rs M sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/InhabRep.lean#L47-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/InhabRep.lean#L47-L54

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep
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

theorem ReciprocityTheory.ChartRestriction.DS.rsM_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : rsM A - rsM B = rsM (A - B) := by sorry
