-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_gval_perm
-- name    : ReciprocityTheory.ChartRestriction.DS.gval_perm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:51:06.484618+00:00
-- url     : https://prove2.me/theorems/8da9ae32-0113-4c3c-b811-8dfc9618c00d
-- title:
--   DS: gval perm
-- statement:
--   The DS construction uses the gval perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/GelfandSeries.lean#L80-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/GelfandSeries.lean#L80-L84

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

theorem ReciprocityTheory.ChartRestriction.DS.gval_perm (l : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (k : ℕ) : gval (l ∘ σ) k = gval l k := by sorry
