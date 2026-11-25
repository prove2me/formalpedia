-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefC_pow_entry_le
-- name    : ReciprocityTheory.ChartRestriction.DS.coefC_pow_entry_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:50:10.119394+00:00
-- url     : https://prove2.me/theorems/5c1b1dce-8b03-4a7d-870c-362255dd8567
-- title:
--   DS: coef C pow entry le
-- statement:
--   The DS construction uses the coef C pow entry le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefCExpEntrySummable.lean#L11-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefCExpEntrySummable.lean#L11-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefCExpEntrySummable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.coefC_pow_entry_le (B : Matrix (Fin n) (Fin n) ℂ) (j : ℕ) (c d : Fin n) :
    ‖(B ^ j) c d‖ ≤ (∑ a, ∑ b, ‖B a b‖) ^ j := by sorry
