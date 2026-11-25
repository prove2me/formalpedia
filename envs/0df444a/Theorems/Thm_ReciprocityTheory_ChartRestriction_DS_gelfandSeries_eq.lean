-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_gelfandSeries_eq
-- name    : ReciprocityTheory.ChartRestriction.DS.gelfandSeries_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:50:45.311679+00:00
-- url     : https://prove2.me/theorems/c996c489-ab04-5a20-82c8-560a3256be66
-- title:
--   DS: gelfand Series eq
-- statement:
--   The DS construction uses the gelfand Series eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/GelfandSeries.lean#L68-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/GelfandSeries.lean#L68-L74

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

theorem ReciprocityTheory.ChartRestriction.DS.gelfandSeries_eq (l : Fin n → ℂ) :
    gelfandSeries l = PowerSeries.X * ∑ r, gxSeries l r := by sorry
