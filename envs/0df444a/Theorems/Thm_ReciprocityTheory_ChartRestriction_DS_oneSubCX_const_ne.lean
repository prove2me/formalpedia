-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_oneSubCX_const_ne
-- name    : ReciprocityTheory.ChartRestriction.DS.oneSubCX_const_ne
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:52:47.686743+00:00
-- url     : https://prove2.me/theorems/4c9849ff-a44a-5680-ba3f-0aae038dcdc7
-- title:
--   DS: one Sub CX const ne
-- statement:
--   The DS construction uses the one Sub CX const ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/GelfandSeries.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/GelfandSeries.lean#L36-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandSeries
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

theorem ReciprocityTheory.ChartRestriction.DS.oneSubCX_const_ne (a : ℂ) : PowerSeries.constantCoeff (1 - PowerSeries.C a * PowerSeries.X) ≠ 0 := by sorry
