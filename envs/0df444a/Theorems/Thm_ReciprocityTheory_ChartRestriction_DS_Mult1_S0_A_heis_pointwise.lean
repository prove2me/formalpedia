-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_A_heis_pointwise
-- name    : ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A.heis_pointwise
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:44:02.297817+00:00
-- url     : https://prove2.me/theorems/b98c7d16-9f6d-4852-9a83-4fd3d8715736
-- title:
--   A: heis pointwise
-- statement:
--   The A construction uses the heis pointwise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/HermitianMeasures/NHeisInt.lean#L34-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/HermitianMeasures/NHeisInt.lean#L34-L56

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

theorem ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A.heis_pointwise (m : ℕ) {d : ℝ} (hd : 0 ≤ d) (x : (Fin m → ℂ) × ℝ) :
    (1 + ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) ^ (-(d / 2)) ≤
      (2 : ℝ) ^ (d / 2) * (1 + ‖x‖) ^ (-d) := by sorry
