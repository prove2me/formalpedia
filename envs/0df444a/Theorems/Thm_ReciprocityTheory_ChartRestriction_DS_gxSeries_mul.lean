-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_gxSeries_mul
-- name    : ReciprocityTheory.ChartRestriction.DS.gxSeries_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:51:20.370173+00:00
-- url     : https://prove2.me/theorems/cb2ab00c-a13c-43fd-8f60-26fcbed414bb
-- title:
--   DS: gx Series mul
-- statement:
--   The DS construction uses the gx Series mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/GelfandSeries.lean#L24-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/GelfandSeries.lean#L24-L34

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

theorem ReciprocityTheory.ChartRestriction.DS.gxSeries_mul (l : Fin n → ℂ) (r : Fin n) :
    gxSeries l r * (1 - PowerSeries.C (l r) * PowerSeries.X) =
      1 - PowerSeries.X * ∑ s ∈ univ.filter (fun s => r < s), gxSeries l s := by sorry
