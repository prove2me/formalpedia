-- Prove2me | Theorems.Thm_WeightedCache_near_card_gibbs
-- name    : WeightedCache.near_card_gibbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:26:18.379109+00:00
-- url     : https://prove2.me/theorems/a0f3ce68-caf8-4ca2-8631-6fdb2ab272d6
-- title:
--   Weighted Cache: near card gibbs
-- statement:
--   The Weighted Cache construction uses the near card gibbs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L124-L144
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Cache.lean#L124-L144

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

theorem WeightedCache.near_card_gibbs {N : ℕ} (c : Fin 3 → ℕ) (Q : Word N) (D : ℕ)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (near c Q D).card * z ^ D ≤
      ∏ i : Fin N, ∑ r : Fin 3, digitWeight c z (Q i) r := by sorry
