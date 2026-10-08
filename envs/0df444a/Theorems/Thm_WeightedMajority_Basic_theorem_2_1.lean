-- Prove2me | Theorems.Thm_WeightedMajority_Basic_theorem_2_1
-- name    : WeightedMajority.Basic.theorem_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:43.374738+00:00
-- url     : https://prove2.me/theorems/235e9011-ba68-4ec5-8add-b07174ac1254
-- title:
--   Theorem 2.1 — WM mistake bound from initial and final weights
-- statement:
--   Let WM use any factor $0\le\beta<1$ and any strictly positive initial weights on a finite pool. On an arbitrary finite sequence of binary predictions and labels, let $m$ be the number of mistakes made by the master, and let $W_0$ and $W_T$ be the initial and final total pool weights. Every legal WM run with $W_T>0$ satisfies
--
--   $$
--   m\le\frac{\log(W_0/W_T)}{\log\!\left(2/(1+\beta)\right)}.
--   $$
--
--   The bound measures the master's mistakes by the decrease in the pool's total weight and applies without a distributional assumption on the sequence.
--
--   **Formalization Note** Both logarithms are natural; their common base cancels, as specified on p. 220. When $\beta=0$ and $W_T=0$, the paper says the logarithmic bound becomes vacuous (infinite). The explicit $W_T>0$ condition excludes exactly that case while retaining the Halving Algorithm case $\beta=0$ whenever its final weight is positive.
-- source:
--   Littlestone and Warmuth, The Weighted Majority Algorithm, Information and Computation 108(2) (1994), p. 221, Theorem 2.1; https://doi.org/10.1006/inco.1994.1009

import Mathlib
import Definitions.Def_WeightedMajority_Basic_IsWMRun

namespace WeightedMajority.Basic

/-- Littlestone and Warmuth's Theorem 2.1. -/
theorem theorem_2_1 {n T : ℕ} (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β < 1)
    (initial : Fin n → ℝ) (hinitial : ∀ i, 0 < initial i)
    (x : Fin T → Fin n → Bool) (label : Fin T → Bool)
    (w : ℕ → Fin n → ℝ) (prediction : Fin T → Bool)
    (hrun : IsWMRun β initial x label w prediction)
    (hfinal : 0 < totalWeight w T) :
    (mistakeCount prediction label : ℝ) ≤
      Real.log (totalWeight w 0 / totalWeight w T) /
        Real.log (2 / (1 + β)) := by sorry

end WeightedMajority.Basic
