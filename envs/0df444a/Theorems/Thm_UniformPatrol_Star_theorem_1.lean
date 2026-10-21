-- Prove2me | Theorems.Thm_UniformPatrol_Star_theorem_1
-- name    : UniformPatrol.Star.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:51.019982+00:00
-- url     : https://prove2.me/theorems/d0dc2307-a983-4c2f-ba1e-7d2e85932fd8
-- title:
--   Theorem 1 — optimal delay and reflection, with both uniqueness regimes
-- statement:
--   For every star with $n\geq2$ defended end nodes and every attack duration $m\geq2$, there is an optimal patroller strategy with reflection probability $s=1$ that forms a saddle point with an attack of delay $d=2$ at any end. Moreover,
--
--   $$\begin{aligned}
--   &\text{every optimal attacker strategy has }d=2\quad\Longleftrightarrow\quad m\text{ is even},\\
--   &\text{every optimal patroller strategy has }s=1\quad\Longleftrightarrow\quad m\geq3.
--   \end{aligned}$$
--
--   The result identifies the robust choices of both players and exactly when those choices are forced.
--
--   **Formalization Note** Optimal means being a component of a pure saddle point over all admissible $(p,s)$ and $(A,d)$. The original star, conditional hitting-time payoff, and all delays remain in the definitions. The $n\geq2$ condition is added because at $n=1$ there is no other end and some conditioning events have probability zero.
-- source:
--   Alpern, Chleboun, Katsikas, The Uniformed Patroller Game, arXiv:1908.07366v2, p. 10 (PDF 11), Theorem 1

import Mathlib
import Definitions.Def_UniformPatrol_Star_Model

namespace UniformPatrol.Star

/-- Theorem 1: delay two and full reflection are optimal, with the stated uniqueness regimes. -/
theorem theorem_1 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) :
    (∃ x : PStrat n, x.s = 1 ∧
      ∀ a : AStrat n, a.d = 2 → IsSaddle n m x a) ∧
    ((∀ a : AStrat n, IsOptimalA n m a → a.d = 2) ↔ Even m) ∧
    ((∀ x : PStrat n, IsOptimalP n m x → x.s = 1) ↔ 3 ≤ m) := by sorry

end UniformPatrol.Star
