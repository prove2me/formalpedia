-- Prove2me | Theorems.Thm_WeightedCache_bank_downward_closed
-- name    : WeightedCache.bank_downward_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:25:21.749846+00:00
-- url     : https://prove2.me/theorems/6a696594-cf8b-4fc9-8bd9-fb3122b85cfb
-- title:
--   Weighted Cache: bank downward closed
-- statement:
--   The Weighted Cache construction uses the bank downward closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L50-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L50-L53

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

theorem WeightedCache.bank_downward_closed {N T : ℕ} {c : Fin 3 → ℕ} (hc : Monotone c)
    {R Q : Word N} (h : Below R Q) (hQ : Q ∈ bank N c T) : R ∈ bank N c T := by sorry
