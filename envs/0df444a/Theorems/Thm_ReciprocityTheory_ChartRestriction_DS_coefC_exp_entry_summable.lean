-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefC_exp_entry_summable
-- name    : ReciprocityTheory.ChartRestriction.DS.coefC_exp_entry_summable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:00.902806+00:00
-- url     : https://prove2.me/theorems/abe79c51-7ff3-4912-b004-3569f3968d5b
-- title:
--   DS: coef C exp entry summable
-- statement:
--   The DS construction uses the coef C exp entry summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefCExpEntrySummable.lean#L34-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefCExpEntrySummable.lean#L34-L43

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

theorem ReciprocityTheory.ChartRestriction.DS.coefC_exp_entry_summable (B : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (c d : Fin n) :
    Summable fun j : ℕ => ‖(s : ℂ) ^ j / (j.factorial : ℂ) * (B ^ j) c d‖ := by sorry
