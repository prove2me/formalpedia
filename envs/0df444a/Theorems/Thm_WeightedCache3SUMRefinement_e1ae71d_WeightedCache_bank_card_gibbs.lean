-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_bank_card_gibbs
-- name    : WeightedCache3SUMRefinement_e1ae71d.WeightedCache.bank_card_gibbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:06:01.656252+00:00
-- url     : https://prove2.me/theorems/f16d5511-c5e8-4aba-90fe-e01c2c441e1e
-- title:
--   bank_card_gibbs
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Cache.lean#L86-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Cache.lean#L86-L99

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

theorem WeightedCache3SUMRefinement_e1ae71d.WeightedCache.bank_card_gibbs (N : ℕ) (c : Fin 3 → ℕ) (T : ℕ)
    (y : ℝ) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    (bank N c T).card * y ^ T ≤ (∑ d : Fin 3, y ^ c d) ^ N := by sorry
