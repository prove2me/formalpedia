-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_ternary_digit_polynomial
-- name    : WeightedCache3SUMRefinement_e1ae71d.WeightedCache.ternary_digit_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:06:01.657181+00:00
-- url     : https://prove2.me/theorems/52788e7d-2f00-435d-86bc-1c166655ae62
-- title:
--   ternary_digit_polynomial
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Cache.lean#L146-L151
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Cache.lean#L146-L151

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Cache
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open WeightedCache3SUMRefinement_e1ae71d.WeightedCache
open Finset

theorem WeightedCache3SUMRefinement_e1ae71d.WeightedCache.ternary_digit_polynomial (a b : ℕ) (z : ℝ) (q : Fin 3) :
    (∑ r : Fin 3, digitWeight ![0, a, b] z q r) =
      if q = 0 then 1 else if q = 1 then 1 + z ^ a else
        1 + z ^ (b - a) + z ^ b := by sorry
