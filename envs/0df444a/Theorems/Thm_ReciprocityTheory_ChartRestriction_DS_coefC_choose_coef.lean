-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefC_choose_coef
-- name    : ReciprocityTheory.ChartRestriction.DS.coefC_choose_coef
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:51:13.115639+00:00
-- url     : https://prove2.me/theorems/83159faa-fcf6-4934-8a44-14811985a39d
-- title:
--   DS: coef C choose coef
-- statement:
--   The DS construction uses the coef C choose coef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefCExpEntrySummable.lean#L74-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefCExpEntrySummable.lean#L74-L81

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

theorem ReciprocityTheory.ChartRestriction.DS.coefC_choose_coef (s : ℂ) (j k : ℕ) :
    s ^ (j + k) / ((j + k).factorial : ℂ) * ((j + k).choose j : ℂ) =
      s ^ j / (j.factorial : ℂ) * (s ^ k / (k.factorial : ℂ)) := by sorry
