-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_weighted_bank_contains_base
-- name    : WeightedCache3SUMRefinement_e1ae71d.WeightedCache.weighted_bank_contains_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:06:25.227773+00:00
-- url     : https://prove2.me/theorems/85d4fe09-516b-4551-a94c-800090005f5e
-- title:
--   weighted_bank_contains_base
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Cache.lean#L244-L251
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Cache.lean#L244-L251

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

theorem WeightedCache3SUMRefinement_e1ae71d.WeightedCache.weighted_bank_contains_base {N h T C : ℕ} (c : Fin 3 → ℕ)
    (hc : ∀ d, c d ≤ C * d.val) (hcut : C * h ≤ T)
    (R : Word N) (hR : rank R ≤ h) : R ∈ bank N c T := by sorry
