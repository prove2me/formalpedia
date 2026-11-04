-- Prove2me | Theorems.Thm_WeightedCache_bank_card_gibbs
-- name    : WeightedCache.bank_card_gibbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:26:12.004126+00:00
-- url     : https://prove2.me/theorems/ac7aeb90-8dab-43f7-ada5-2121390ef2b4
-- title:
--   Weighted Cache: bank card gibbs
-- statement:
--   The Weighted Cache construction uses the bank card gibbs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L86-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L86-L99

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

theorem WeightedCache.bank_card_gibbs (N : ℕ) (c : Fin 3 → ℕ) (T : ℕ)
    (y : ℝ) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    (bank N c T).card * y ^ T ≤ (∑ d : Fin 3, y ^ c d) ^ N := by sorry
