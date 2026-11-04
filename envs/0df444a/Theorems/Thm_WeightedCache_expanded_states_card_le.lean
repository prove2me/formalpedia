-- Prove2me | Theorems.Thm_WeightedCache_expanded_states_card_le
-- name    : WeightedCache.expanded_states_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:28:03.623012+00:00
-- url     : https://prove2.me/theorems/2af354be-16e3-4f77-bda7-41a28dd01b43
-- title:
--   Weighted Cache: expanded states card le
-- statement:
--   The Weighted Cache construction uses the expanded states card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L290-L297
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L290-L297

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

theorem WeightedCache.expanded_states_card_le {N T : ℕ} (c : Fin 3 → ℕ) (hc : Monotone c)
    (Q : Word N) (S : Finset (Word N))
    (hS : ∀ R ∈ S, Below R Q ∧ R ∉ bank N c T) :
    S.card ≤ (near c Q (cost c Q - (T + 1))).card := by sorry
