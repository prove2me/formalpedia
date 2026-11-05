-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_expanded_states_card_le
-- name    : WeightedCache3SUMRefinement_e1ae71d.WeightedCache.expanded_states_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:06:50.769646+00:00
-- url     : https://prove2.me/theorems/96437e0a-66e7-4dbb-852b-568a31c4364d
-- title:
--   expanded_states_card_le
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Cache.lean#L290-L297
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Cache.lean#L290-L297

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

theorem WeightedCache3SUMRefinement_e1ae71d.WeightedCache.expanded_states_card_le {N T : ℕ} (c : Fin 3 → ℕ) (hc : Monotone c)
    (Q : Word N) (S : Finset (Word N))
    (hS : ∀ R ∈ S, Below R Q ∧ R ∉ bank N c T) :
    S.card ≤ (near c Q (cost c Q - (T + 1))).card := by sorry
