-- Prove2me | Theorems.Thm_UniformPatrol_Star_proposition_1
-- name    : UniformPatrol.Star.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:51.673515+00:00
-- url     : https://prove2.me/theorems/e13e0096-7e71-451b-828e-6a30b0bdc36d
-- title:
--   Proposition 1 — duration-two optimizer and value
-- statement:
--   For attack duration $m=2$ and $n\geq2$, the centre-to-end probability $\hat p=1-\sqrt{n(n-1)}/n$ with full reflection is optimal. Delay two at any end forms a saddle point with it. The game value is
--
--   $$V=(2n-1)-2\sqrt{n(n-1)}.$$
--
--   Every optimal attacker strategy has delay two. There is also a number $k<1$ such that all admissible patroller strategies $(\hat p,s)$ with $s\geq k$ are optimal. This is the duration-two exception to uniqueness of full reflection.
--
--   **Formalization Note** The paper says to locate at a random end. The full star is symmetric, so each pure choice of end has the same saddle payoff. The mission assumes $n\geq2$.
-- source:
--   Alpern, Chleboun, Katsikas, The Uniformed Patroller Game, arXiv:1908.07366v2, p. 4 (PDF 5), Proposition 1 and eqs. (1)–(2)

import Mathlib
import Definitions.Def_UniformPatrol_Star_Model

namespace UniformPatrol.Star

/-- Proposition 1: the square-root optimum, unique delay, and a nontrivial range of reflections. -/
theorem proposition_1 (n : ℕ) (hn : 2 ≤ n) :
    ∃ x : PStrat n,
      x.p = 1 - Real.sqrt ((n : ℝ) * ((n : ℝ) - 1)) / (n : ℝ) ∧
      x.s = 1 ∧
      (∀ a : AStrat n, a.d = 2 → IsSaddle n 2 x a) ∧
      (∀ a : AStrat n, a.d = 2 →
        Q n 2 x a = (2 * (n : ℝ) - 1) -
          2 * Real.sqrt ((n : ℝ) * ((n : ℝ) - 1))) ∧
      (∀ a : AStrat n, IsOptimalA n 2 a → a.d = 2) ∧
      (∃ k : ℝ, k < 1 ∧ ∀ x' : PStrat n,
        x'.p = 1 - Real.sqrt ((n : ℝ) * ((n : ℝ) - 1)) / (n : ℝ) →
        k ≤ x'.s → IsOptimalP n 2 x') := by sorry

end UniformPatrol.Star
