-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rsM_mul
-- name    : ReciprocityTheory.ChartRestriction.DS.rsM_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:56:40.849801+00:00
-- url     : https://prove2.me/theorems/e1e0d5b3-52e9-5a2f-ba22-29b6a32c428f
-- title:
--   DS: rs M mul
-- statement:
--   The DS construction uses the rs M mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/InhabRep.lean#L38-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/InhabRep.lean#L38-L45

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

theorem ReciprocityTheory.ChartRestriction.DS.rsM_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : rsM A * rsM B = rsM (A * B) := by sorry
