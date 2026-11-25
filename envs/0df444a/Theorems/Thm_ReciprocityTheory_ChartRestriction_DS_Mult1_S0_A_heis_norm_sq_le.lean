-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_A_heis_norm_sq_le
-- name    : ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A.heis_norm_sq_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:43:52.785656+00:00
-- url     : https://prove2.me/theorems/e14644c4-8849-53ad-8789-38b1cbaa0835
-- title:
--   A: heis norm sq le
-- statement:
--   The A construction uses the heis norm sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/HermitianMeasures/NHeisInt.lean#L10-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/HermitianMeasures/NHeisInt.lean#L10-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_HermitianMeasures_NHeisInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.S0 ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

theorem ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A.heis_norm_sq_le (m : ℕ) (x : (Fin m → ℂ) × ℝ) :
    ‖x‖ ^ 2 ≤ ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2 := by sorry
