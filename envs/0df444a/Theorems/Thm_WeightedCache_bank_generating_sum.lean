-- Prove2me | Theorems.Thm_WeightedCache_bank_generating_sum
-- name    : WeightedCache.bank_generating_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:25:50.098979+00:00
-- url     : https://prove2.me/theorems/a49658bc-b49b-4d98-bf6e-303bd2f14175
-- title:
--   Weighted Cache: bank generating sum
-- statement:
--   The Weighted Cache construction uses the bank generating sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L73-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L73-L78

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

theorem WeightedCache.bank_generating_sum (N : ℕ) (c : Fin 3 → ℕ) (y : ℝ) :
    (∑ R : Word N, y ^ cost c R) = (∑ d : Fin 3, y ^ c d) ^ N := by sorry
