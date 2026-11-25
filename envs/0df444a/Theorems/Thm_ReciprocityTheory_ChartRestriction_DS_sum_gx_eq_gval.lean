-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sum_gx_eq_gval
-- name    : ReciprocityTheory.ChartRestriction.DS.sum_gx_eq_gval
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:54:17.961845+00:00
-- url     : https://prove2.me/theorems/ba4789d7-e0c0-5fec-97f2-c4f4b2205298
-- title:
--   DS: sum gx eq gval
-- statement:
--   The DS construction uses the sum gx eq gval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/GelfandSeries.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/GelfandSeries.lean#L76-L78

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

theorem ReciprocityTheory.ChartRestriction.DS.sum_gx_eq_gval (l : Fin n → ℂ) (k : ℕ) : ∑ r, gx l k r = gval l k := by sorry
