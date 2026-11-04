-- Prove2me | Theorems.Thm_WeightedCache_below_bank_or_near
-- name    : WeightedCache.below_bank_or_near
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:25:47.678581+00:00
-- url     : https://prove2.me/theorems/f8986c4a-0dcd-4196-bf92-268e86b2c634
-- title:
--   Weighted Cache: below bank or near
-- statement:
--   The Weighted Cache construction uses the below bank or near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L63-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L63-L71

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

theorem WeightedCache.below_bank_or_near {N T : ℕ} {c : Fin 3 → ℕ} (hc : Monotone c)
    {R Q : Word N} (h : Below R Q) :
    R ∈ bank N c T ∨ R ∈ near c Q (cost c Q - (T + 1)) := by sorry
