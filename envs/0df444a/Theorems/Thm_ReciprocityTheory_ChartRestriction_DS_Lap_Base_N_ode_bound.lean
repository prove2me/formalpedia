-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_ode_bound
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.ode_bound
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:41:33.148205+00:00
-- url     : https://prove2.me/theorems/331a91de-0cf4-43eb-8c8c-989b3de95858
-- title:
--   N: ode bound
-- statement:
--   The N construction uses the ode bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/OneParam.lean#L8-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/OneParam.lean#L8-L58

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_OneParam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Filter Topology
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.ode_bound (U U' : ℝ → ℂ) (a b : ℂ) (ha : a.re = 0) {δ : ℝ} (hU0 : U 0 = 1)
    (hder : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt U (U' s) s)
    (hb : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖U' s - (a + s * b) * U s‖ ≤ δ) :
    ‖U 1 * cexp (-a) - cexp (b / 2)‖ ≤ δ * Real.exp ‖b‖ := by sorry
