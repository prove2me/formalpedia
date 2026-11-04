-- Prove2me | Theorems.Thm_WeightedCache_ternary_digit_polynomial
-- name    : WeightedCache.ternary_digit_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:26:33.696627+00:00
-- url     : https://prove2.me/theorems/998e913b-0dc9-408c-ab7b-50d2486bfae6
-- title:
--   Weighted Cache: ternary digit polynomial
-- statement:
--   The Weighted Cache construction uses the ternary digit polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L146-L151
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L146-L151

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
import Definitions.Def_Submission_Weighted_Cache
set_option autoImplicit false
open WeightedCache
open Finset

theorem WeightedCache.ternary_digit_polynomial (a b : ℕ) (z : ℝ) (q : Fin 3) :
    (∑ r : Fin 3, digitWeight ![0, a, b] z q r) =
      if q = 0 then 1 else if q = 1 then 1 + z ^ a else
        1 + z ^ (b - a) + z ^ b := by sorry
