-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_exists_high_degree_low_bad_degree
-- name    : QEC.Coding.SmallSetExpansion.exists_high_degree_low_bad_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:29:38.395185+00:00
-- url     : https://prove2.me/theorems/d6e7453a-7472-4a95-a443-9d93734e0897
-- title:
--   Small Set Expansion: exists high degree low bad degree
-- statement:
--   Simultaneous degree selection from two actual finite sums. The final
--   budget inequality compares the Markov loss with the high-degree fraction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/DegreeSelection.lean#L19-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/DegreeSelection.lean#L19-L76

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_DegreeSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u

theorem QEC.Coding.SmallSetExpansion.exists_high_degree_low_bad_degree
    {V : Type u} (T : Finset V) (hT : T.Nonempty) (useful bad : V → ℝ)
    (maximum threshold badAverage badCutoff : ℝ)
    (hMaximum : 0 < maximum) (hThreshold : 0 < threshold)
    (hCutoff : 0 ≤ badCutoff)
    (hUseful : ∀ v ∈ T, useful v ≤ maximum)
    (hBadNonnegative : ∀ v ∈ T, 0 ≤ bad v)
    (hUsefulAverage : 2 * threshold * T.card ≤ ∑ v ∈ T, useful v)
    (hBadAverage : (∑ v ∈ T, bad v) ≤ badAverage * T.card)
    (hBudgets : badAverage * maximum ≤ badCutoff * threshold) :
    ∃ v ∈ T, threshold ≤ useful v ∧ bad v ≤ badCutoff := by sorry
