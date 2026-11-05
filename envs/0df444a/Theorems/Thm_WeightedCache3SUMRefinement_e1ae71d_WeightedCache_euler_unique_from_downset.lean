-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_euler_unique_from_downset
-- name    : WeightedCache3SUMRefinement_e1ae71d.WeightedCache.euler_unique_from_downset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:06:22.06726+00:00
-- url     : https://prove2.me/theorems/d2067ccb-310d-4e51-9add-621bfc926a9d
-- title:
--   euler_unique_from_downset
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Cache.lean#L213-L242
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Cache.lean#L213-L242

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

theorem WeightedCache3SUMRefinement_e1ae71d.WeightedCache.euler_unique_from_downset {N h : ℕ} (B : Finset (Word N))
    (hbase : ∀ R, rank R ≤ h → R ∈ B) (F G : Word N → ℤ)
    (hF : ∀ R, (∑ i : Fin N, (R i).val * F (predecessor R i)) =
      ((rank R : ℤ) - (h : ℤ)) * F R)
    (hG : ∀ R, (∑ i : Fin N, (R i).val * G (predecessor R i)) =
      ((rank R : ℤ) - (h : ℤ)) * G R)
    (hbank : ∀ R ∈ B, F R = G R) : F = G := by sorry
