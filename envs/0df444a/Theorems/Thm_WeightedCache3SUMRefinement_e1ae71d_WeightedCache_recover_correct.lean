-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_recover_correct
-- name    : WeightedCache3SUMRefinement_e1ae71d.WeightedCache.recover_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:06:14.576016+00:00
-- url     : https://prove2.me/theorems/0d41ac6b-f408-4d68-b4c8-ab1a1af905f3
-- title:
--   recover_correct
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Cache.lean#L308-L336
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Cache.lean#L308-L336

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

theorem WeightedCache3SUMRefinement_e1ae71d.WeightedCache.recover_correct {N h : ℕ} (B : Finset (Word N))
    (hbase : ∀ R, rank R ≤ h → R ∈ B) (values F : Word N → ℤ)
    (hbank : ∀ R ∈ B, values R = F R)
    (hF : ∀ R, (∑ i : Fin N, (R i).val * F (predecessor R i)) =
      ((rank R : ℤ) - (h : ℤ)) * F R) :
    ∀ k R, rank R ≤ k → recover B values h k R = F R := by sorry
