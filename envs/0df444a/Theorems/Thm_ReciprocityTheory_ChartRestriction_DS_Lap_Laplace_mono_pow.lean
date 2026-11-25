-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Laplace_mono_pow
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Laplace.mono_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:42:22.359694+00:00
-- url     : https://prove2.me/theorems/f467602b-fbd1-42e1-bb8d-bd667f557bd5
-- title:
--   Laplace: mono pow
-- statement:
--   The Laplace construction uses the mono pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/Laplace.lean#L194-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/Laplace.lean#L194-L212

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_Laplace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Filter Topology Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Laplace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Laplace.mono_pow {x s t : ℝ} (hx : 0 ≤ x) (hs : 0 < s) (hst : s ≤ t) :
    (1 + x / s) ^ s ≤ (1 + x / t) ^ t := by sorry
