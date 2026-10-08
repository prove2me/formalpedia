-- Prove2me | Theorems.Thm_WeightedMajority_Basic_mistake_weight_step
-- name    : WeightedMajority.Basic.mistake_weight_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:47.218639+00:00
-- url     : https://prove2.me/theorems/ca75fc6e-c5c0-4ef5-be1e-21f09d62024c
-- title:
--   Section 2 — total-weight contraction on a WM mistake
-- statement:
--   Let WM use factor $0\le\beta<1$ and strictly positive initial weights on a finite pool. Consider any finite binary sequence and any legal WM run. If the master errs on trial $t$, the total pool weight after that trial is at most $(1+\beta)/2$ times its weight before the trial:
--
--   $$
--   W_{t+1}\le \frac{1+\beta}{2}W_t.
--   $$
--
--   This is the local weight estimate in the proof of Theorem 2.1. It applies to either permitted tie choice.
--
--   **Formalization Note** The statement uses a weight inequality, which remains meaningful when a later weight is zero; no division by the current weight is needed.
-- source:
--   Littlestone and Warmuth, The Weighted Majority Algorithm, Information and Computation 108(2) (1994), p. 221, §2, proof of Theorem 2.1; https://doi.org/10.1006/inco.1994.1009

import Mathlib
import Definitions.Def_WeightedMajority_Basic_IsWMRun

namespace WeightedMajority.Basic

/-- The per-mistake weight estimate used in the proof of Theorem 2.1. -/
theorem mistake_weight_step {n T : ℕ} (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β < 1)
    (initial : Fin n → ℝ) (hinitial : ∀ i, 0 < initial i)
    (x : Fin T → Fin n → Bool) (label : Fin T → Bool)
    (w : ℕ → Fin n → ℝ) (prediction : Fin T → Bool)
    (hrun : IsWMRun β initial x label w prediction)
    (t : Fin T) (hmistake : prediction t ≠ label t) :
    totalWeight w (t.val + 1) ≤ ((1 + β) / 2) * totalWeight w t.val := by sorry

end WeightedMajority.Basic
