-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_S0_A_heis_lint_fin
-- name    : ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A.heis_lint_fin
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:42:48.864204+00:00
-- url     : https://prove2.me/theorems/67b9fe44-f9c4-5b82-9ad3-21472f3dc33d
-- title:
--   A: heis lint fin
-- statement:
--   The A construction uses the heis lint fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/HermitianMeasures/NHeisInt.lean#L58-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/HermitianMeasures/NHeisInt.lean#L58-L87

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

theorem ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A.heis_lint_fin (m : ℕ) {d : ℝ} (hd : (2 * m + 1 : ℝ) < d) :
    ∫⁻ x : (Fin m → ℂ) × ℝ, ENNReal.ofReal ((1 + ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) ^ (-(d / 2))) < ∞ := by sorry
