-- Prove2me | Theorems.Thm_VanderbeiLP_SelfDual_self_dual_embedding_solution
-- name    : VanderbeiLP.SelfDual.self_dual_embedding_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T13:54:12.967066+00:00
-- url     : https://prove2.me/theorems/3e280db7-177f-4dbf-95cb-d370944a6526
-- title:
--   Theorem 22.8 — a strictly complementary solution of the self-dual embedding solves the LP or certifies infeasibility
-- statement:
--   Let $A$ be a real $m \times n$ matrix, $b \in \mathbb{R}^m$, $c \in \mathbb{R}^n$, and consider the primal problem (22.1) $\max c^Tx$ s.t. $Ax \le b$, $x \ge 0$, its dual (22.2) $\min b^Ty$ s.t. $A^Ty \ge c$, $y \ge 0$, and the self-dual embedding (22.21)
--
--   $$-A^T y + c\phi + z = 0,\qquad Ax - b\phi + w = 0,\qquad -c^T x + b^T y + \psi = 0,\qquad x, y, \phi, z, w, \psi \ge 0.$$
--
--   Suppose that $(\bar x, \bar y, \bar\phi, \bar z, \bar w, \bar\psi)$ is a strictly complementary feasible solution of (22.21): $\bar x_j + \bar z_j > 0$ for all $j$, $\bar y_i + \bar w_i > 0$ for all $i$, and $\bar\phi + \bar\psi > 0$.
--
--   1. If $\bar\phi > 0$, then $x^* = \bar x/\bar\phi$ is optimal for the primal problem (22.1) and $y^* = \bar y/\bar\phi$ is optimal for its dual (22.2).
--   2. If $\bar\phi = 0$, then either $c^T\bar x > 0$ or $b^T\bar y < 0$ (possibly both), and
--      - (a) if $c^T\bar x > 0$, then the dual problem is infeasible;
--      - (b) if $b^T\bar y < 0$, then the primal problem is infeasible.
--
--   This is what makes the homogeneous self-dual method a complete algorithm for linear programming: a strictly complementary solution of one auxiliary problem, which always has feasible solutions, either yields a primal–dual optimal pair or proves that one of the two problems is infeasible.
--
--   **Formalization Note** The book's parenthetical "(hence, optimal)" in the hypothesis is not formalized: every feasible solution of (22.21) is optimal, its objective being $0$. "Either … or" in (2) is the inclusive or, as the book's proof says. Division by $\bar\phi$ is written as scalar multiplication by $\bar\phi^{-1}$ and only occurs under $\bar\phi > 0$.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 334, Theorem 22.8 and Eq. (22.21) (PDF p. 340); problems (22.1)–(22.2) on p. 323 (PDF p. 329)

import Mathlib
import Definitions.Def_VanderbeiLP_SelfDual_SelfDualEmbedding

open Matrix

namespace VanderbeiLP.SelfDual

/-- Theorem 22.8 (Vanderbei, p. 334). Let `(x̄, ȳ, φ̄, z̄, w̄, ψ̄)` be a strictly complementary
feasible solution of the self-dual embedding (22.21) of the primal (22.1)
`max cᵀx, Ax ≤ b, x ≥ 0` and its dual (22.2) `min bᵀy, Aᵀy ≥ c, y ≥ 0`.
(1) If `φ̄ > 0`, then `x̄/φ̄` is optimal for (22.1) and `ȳ/φ̄` is optimal for (22.2).
(2) If `φ̄ = 0`, then `cᵀx̄ > 0` or `bᵀȳ < 0`; (a) if `cᵀx̄ > 0` the dual is infeasible;
(b) if `bᵀȳ < 0` the primal is infeasible. -/
theorem self_dual_embedding_solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (φ : ℝ) (z : Fin n → ℝ) (w : Fin m → ℝ) (ψ : ℝ)
    (hfeas : EmbeddingFeasible A b c x y φ z w ψ)
    (hsc : EmbeddingStrictlyComplementary x y φ z w ψ) :
    (0 < φ → VanderbeiLP.StrictComp.PrimalOptimal A b c (φ⁻¹ • x) ∧ VanderbeiLP.StrictComp.DualOptimal A b c (φ⁻¹ • y)) ∧
    (φ = 0 →
      (0 < c ⬝ᵥ x ∨ b ⬝ᵥ y < 0) ∧
      (0 < c ⬝ᵥ x → ¬ ∃ y' : Fin m → ℝ, DualFeasible A c y') ∧
      (b ⬝ᵥ y < 0 → ¬ ∃ x' : Fin n → ℝ, PrimalFeasible A b x')) := by sorry

end VanderbeiLP.SelfDual
