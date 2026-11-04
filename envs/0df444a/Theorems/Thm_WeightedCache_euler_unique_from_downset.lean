-- Prove2me | Theorems.Thm_WeightedCache_euler_unique_from_downset
-- name    : WeightedCache.euler_unique_from_downset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:27:08.556384+00:00
-- url     : https://prove2.me/theorems/4a07a135-60f1-4e63-98f8-44dbf5619a2d
-- title:
--   Weighted Cache: euler unique from downset
-- statement:
--   The Weighted Cache construction uses the euler unique from downset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L213-L242
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L213-L242

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

theorem WeightedCache.euler_unique_from_downset {N h : ℕ} (B : Finset (Word N))
    (hbase : ∀ R, rank R ≤ h → R ∈ B) (F G : Word N → ℤ)
    (hF : ∀ R, (∑ i : Fin N, (R i).val * F (predecessor R i)) =
      ((rank R : ℤ) - (h : ℤ)) * F R)
    (hG : ∀ R, (∑ i : Fin N, (R i).val * G (predecessor R i)) =
      ((rank R : ℤ) - (h : ℤ)) * G R)
    (hbank : ∀ R ∈ B, F R = G R) : F = G := by sorry
