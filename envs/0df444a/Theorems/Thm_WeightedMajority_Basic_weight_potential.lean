-- Prove2me | Theorems.Thm_WeightedMajority_Basic_weight_potential
-- name    : WeightedMajority.Basic.weight_potential
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:51.55798+00:00
-- url     : https://prove2.me/theorems/d6c0f086-04fd-47d3-9645-00759d1a67f4
-- title:
--   Section 2 — whole-sequence WM weight bound
-- statement:
--   Run WM with factor $0\le\beta<1$ and strictly positive initial weights on any finite binary sequence. Write $m$ for the number of mistakes made by the master, and $W_0$ and $W_T$ for the initial and final total pool weights. Then
--
--   $$
--   W_T\le W_0\left(\frac{1+\beta}{2}\right)^m.
--   $$
--
--   This is the whole-sequence weight estimate stated before Theorem 2.1, with the value of $u$ used in that theorem. It also covers $m=0$ and a zero final weight.
-- source:
--   Littlestone and Warmuth, The Weighted Majority Algorithm, Information and Computation 108(2) (1994), pp. 220–221, §2, discussion preceding Theorem 2.1; https://doi.org/10.1006/inco.1994.1009

import Mathlib
import Definitions.Def_WeightedMajority_Basic_IsWMRun

namespace WeightedMajority.Basic

/-- The whole-sequence weight estimate preceding Theorem 2.1. -/
theorem weight_potential {n T : ℕ} (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β < 1)
    (initial : Fin n → ℝ) (hinitial : ∀ i, 0 < initial i)
    (x : Fin T → Fin n → Bool) (label : Fin T → Bool)
    (w : ℕ → Fin n → ℝ) (prediction : Fin T → Bool)
    (hrun : IsWMRun β initial x label w prediction) :
    totalWeight w T ≤ totalWeight w 0 * ((1 + β) / 2) ^ mistakeCount prediction label := by sorry

end WeightedMajority.Basic
