-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefC_exp_entry_hasSum
-- name    : ReciprocityTheory.ChartRestriction.DS.coefC_exp_entry_hasSum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:51:01.542604+00:00
-- url     : https://prove2.me/theorems/61c382c1-bf66-5821-9448-546ff8d50522
-- title:
--   DS: coef C exp entry has Sum
-- statement:
--   The DS construction uses the coef C exp entry has Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefCExpEntrySummable.lean#L45-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefCExpEntrySummable.lean#L45-L64

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

theorem ReciprocityTheory.ChartRestriction.DS.coefC_exp_entry_hasSum (B : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (c d : Fin n) :
    HasSum (fun j : ℕ => (s : ℂ) ^ j / (j.factorial : ℂ) * (B ^ j) c d)
      ((NormedSpace.exp ((s : ℂ) • B)) c d) := by sorry
