-- Prove2me | Theorems.Thm_ShorNonsmooth_Decomposition_subgradient_formula_differentiable
-- name    : ShorNonsmooth.Decomposition.subgradient_formula_differentiable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T16:24:37.604747+00:00
-- url     : https://prove2.me/theorems/52e8c78a-aab1-42f3-a48d-b81b15f9e46f
-- title:
--   Corollary of Theorem 4.1 — formula (4.7) for functions differentiable in $y$
-- statement:
--   Assume the hypotheses of Theorem 4.1: $f_0$ and $f_i$, $i = 1,\dots,n$, are jointly convex; $W$ is a convex set of $x$-values at which the minimum in (4.5) is attained; $\bar x \in W$ and the Slater condition holds for (4.4) at $\bar x$; $\bar y = y(\bar x)$ is optimal and $U = U(\bar x)$ are Kuhn–Tucker multipliers. Suppose in addition that each $f_\alpha(x,\cdot)$, $\alpha = 0,1,\dots,n$, is continuously differentiable in $y$. Let $(g^x_{f_\alpha}, g^y_{f_\alpha})$ be **arbitrary** subgradients of $f_\alpha$ at $(\bar x,\bar y)$. Then
--   $$
--   g(\bar x) = g^x_{f_0}(\bar x, y(\bar x)) + \sum_{i=1}^n U_i(\bar x)\, g^x_{f_i}(\bar x, y(\bar x)) \qquad (4.7)
--   $$
--   is a subgradient of $\Phi$ at $\bar x$ on $W$: $\Phi(x) - \Phi(\bar x) \ge (x - \bar x, g(\bar x))$ for all $x \in W$.
--
--   Formula (4.7) lets one compute a subgradient of $\Phi$ from subgradients of the problem functions, without choosing a special subgradient of $L_U$; it underlies the decomposition algorithm of p. 96 for linear and quadratic subproblems.
--
--   **Formalization Note** "Continuously differentiable with respect to $y$" is `ContDiff ℝ 1` of $y \mapsto f_\alpha(x,y)$ for every $x$.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 95, Corollary (formula (4.7)); proof p. 96

import Mathlib
import Definitions.Def_ShorNonsmooth_Decomposition_ValueFunction

namespace ShorNonsmooth.Decomposition

/-- Shor (1985), **Corollary** of Theorem 4.1 (p. 95), formula (4.7): under the hypotheses of Theorem 4.1
(jointly convex `f_α`, a convex set `W` on which the minimum (4.5) is attained, `xbar ∈ W` with the Slater
condition, an optimal `ybar` and Kuhn–Tucker multipliers `U`), if in addition every `f_α(x, ·)`,
`α = 0, 1, …, n`, is continuously differentiable in `y`, then for **arbitrary** subgradients
`(gx₀, gy₀)` of `f₀` and `(gx_i, gy_i)` of `f_i` at `(xbar, ybar)`, the vector
`gx₀ + Σ_i U_i gx_i` is a subgradient of `Φ` at `xbar` on `W`. -/
theorem subgradient_formula_differentiable {l m n : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hf₀ : JointlyConvex f₀) (hf : ∀ i, JointlyConvex (f i))
    (hd₀ : ∀ x, ContDiff ℝ 1 (f₀ x)) (hd : ∀ i x, ContDiff ℝ 1 (f i x))
    (W : Set (EuclideanSpace ℝ (Fin l))) (hW : Convex ℝ W)
    (hWmin : ∀ x ∈ W, MinAttained f₀ f x)
    (xbar : EuclideanSpace ℝ (Fin l)) (hxbar : xbar ∈ W) (hslater : SlaterAt f xbar)
    (ybar : EuclideanSpace ℝ (Fin m)) (hybar : IsOptimalY f₀ f xbar ybar)
    (U : Fin n → ℝ) (hU : IsKuhnTuckerMultiplier f₀ f xbar ybar U)
    (gx₀ : EuclideanSpace ℝ (Fin l)) (gy₀ : EuclideanSpace ℝ (Fin m))
    (hg₀ : IsJointSubgradient f₀ xbar ybar gx₀ gy₀)
    (gx : Fin n → EuclideanSpace ℝ (Fin l)) (gy : Fin n → EuclideanSpace ℝ (Fin m))
    (hg : ∀ i, IsJointSubgradient (f i) xbar ybar (gx i) (gy i)) :
    IsSubgradientOn (valueFn f₀ f) W xbar (gx₀ + ∑ i, U i • gx i) := by sorry

end ShorNonsmooth.Decomposition
