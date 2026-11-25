-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_gxSeries_tele
-- name    : ReciprocityTheory.ChartRestriction.DS.gxSeries_tele
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:51:08.767681+00:00
-- url     : https://prove2.me/theorems/c4b039dc-f961-470c-a41a-cc41461580a9
-- title:
--   DS: gx Series tele
-- statement:
--   The DS construction uses the gx Series tele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/GelfandSeries.lean#L44-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/GelfandSeries.lean#L44-L66

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

theorem ReciprocityTheory.ChartRestriction.DS.gxSeries_tele (l : Fin n → ℂ) (d : ℕ) : ∀ r : ℕ, n - r = d →
    1 - PowerSeries.X * ∑ s ∈ univ.filter (fun s : Fin n => r ≤ s.val), gxSeries l s =
      ∏ s ∈ univ.filter (fun s : Fin n => r ≤ s.val),
        (1 - PowerSeries.X * (1 - PowerSeries.C (l s) * PowerSeries.X)⁻¹) := by sorry
