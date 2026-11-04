-- Prove2me | Theorems.Thm_WeightedCache_recover_correct
-- name    : WeightedCache.recover_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:28:05.854393+00:00
-- url     : https://prove2.me/theorems/ceb89c18-c830-4f3a-ad85-fd776fefcb16
-- title:
--   Weighted Cache: recover correct
-- statement:
--   The Weighted Cache construction uses the recover correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L308-L336
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L308-L336

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

theorem WeightedCache.recover_correct {N h : ℕ} (B : Finset (Word N))
    (hbase : ∀ R, rank R ≤ h → R ∈ B) (values F : Word N → ℤ)
    (hbank : ∀ R ∈ B, values R = F R)
    (hF : ∀ R, (∑ i : Fin N, (R i).val * F (predecessor R i)) =
      ((rank R : ℤ) - (h : ℤ)) * F R) :
    ∀ k R, rank R ≤ k → recover B values h k R = F R := by sorry
