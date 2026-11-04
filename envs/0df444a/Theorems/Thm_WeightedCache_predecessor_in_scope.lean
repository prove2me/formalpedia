-- Prove2me | Theorems.Thm_WeightedCache_predecessor_in_scope
-- name    : WeightedCache.predecessor_in_scope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:27:56.336747+00:00
-- url     : https://prove2.me/theorems/82d992ad-faa7-4638-a63f-61b8f866bda4
-- title:
--   Weighted Cache: predecessor in scope
-- statement:
--   The Weighted Cache construction uses the predecessor in scope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L284-L288
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L284-L288

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

theorem WeightedCache.predecessor_in_scope {N T : ℕ} {c : Fin 3 → ℕ} (hc : Monotone c)
    {R Q : Word N} (hRQ : Below R Q) (i : Fin N) :
    predecessor R i ∈ bank N c T ∨
      predecessor R i ∈ near c Q (cost c Q - (T + 1)) := by sorry
