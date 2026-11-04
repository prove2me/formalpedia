-- Prove2me | Theorems.Thm_WeightedCache_deficit_generating_sum
-- name    : WeightedCache.deficit_generating_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:26:14.127737+00:00
-- url     : https://prove2.me/theorems/1dc4e33c-c321-4fe7-8b76-effc8541afc4
-- title:
--   Weighted Cache: deficit generating sum
-- statement:
--   The Weighted Cache construction uses the deficit generating sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L104-L122
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L104-L122

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

theorem WeightedCache.deficit_generating_sum {N : ℕ} (c : Fin 3 → ℕ) (Q : Word N) (z : ℝ) :
    (∑ R : Word N, if Below R Q then z ^ deficit c Q R else 0) =
      ∏ i : Fin N, ∑ r : Fin 3, digitWeight c z (Q i) r := by sorry
