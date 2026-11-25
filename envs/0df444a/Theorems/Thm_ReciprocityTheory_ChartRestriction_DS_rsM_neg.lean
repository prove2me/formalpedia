-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rsM_neg
-- name    : ReciprocityTheory.ChartRestriction.DS.rsM_neg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:53:57.241794+00:00
-- url     : https://prove2.me/theorems/551bac80-4513-496b-b721-1a5d40725f41
-- title:
--   DS: rs M neg
-- statement:
--   The DS construction uses the rs M neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/InhabRep.lean#L65-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/InhabRep.lean#L65-L72

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

theorem ReciprocityTheory.ChartRestriction.DS.rsM_neg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : rsM (-A) = -rsM A := by sorry
