-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_bank_downward_closed
-- name    : WeightedCache3SUMRefinement_e1ae71d.WeightedCache.bank_downward_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:06:23.933887+00:00
-- url     : https://prove2.me/theorems/30d85fbb-51b7-44f2-a0b6-423119488a5d
-- title:
--   bank_downward_closed
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Cache.lean#L50-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Cache.lean#L50-L53

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

theorem WeightedCache3SUMRefinement_e1ae71d.WeightedCache.bank_downward_closed {N T : ℕ} {c : Fin 3 → ℕ} (hc : Monotone c)
    {R Q : Word N} (h : Below R Q) (hQ : Q ∈ bank N c T) : R ∈ bank N c T := by sorry
