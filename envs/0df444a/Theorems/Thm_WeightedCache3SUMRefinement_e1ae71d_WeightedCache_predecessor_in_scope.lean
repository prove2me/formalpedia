-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_predecessor_in_scope
-- name    : WeightedCache3SUMRefinement_e1ae71d.WeightedCache.predecessor_in_scope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:06:53.014216+00:00
-- url     : https://prove2.me/theorems/b1ecc035-4ffc-423c-9ebf-85f39e3faebc
-- title:
--   predecessor_in_scope
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Cache.lean#L284-L288
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Cache.lean#L284-L288

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

theorem WeightedCache3SUMRefinement_e1ae71d.WeightedCache.predecessor_in_scope {N T : ℕ} {c : Fin 3 → ℕ} (hc : Monotone c)
    {R Q : Word N} (hRQ : Below R Q) (i : Fin N) :
    predecessor R i ∈ bank N c T ∨
      predecessor R i ∈ near c Q (cost c Q - (T + 1)) := by sorry
