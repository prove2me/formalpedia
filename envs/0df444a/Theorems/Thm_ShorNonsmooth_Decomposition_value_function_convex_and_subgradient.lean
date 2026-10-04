-- Prove2me | Theorems.Thm_ShorNonsmooth_Decomposition_value_function_convex_and_subgradient
-- name    : ShorNonsmooth.Decomposition.value_function_convex_and_subgradient
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T16:38:09.375492+00:00
-- url     : https://prove2.me/theorems/6b0ef914-dd72-4384-8b37-6644c5a35645
-- title:
--   Theorem 4.1 — the value function of decomposition with respect to variables is convex, with subgradient $g^x_{L_U}(\bar x, y(\bar x))$
-- statement:
--   Let $f_0$ and $f_i$, $i = 1,\dots,n$, be jointly convex functions of $(x,y) \in E^x_l \times E^y_m$, let $D(x) = \{y : f_i(x,y) \le 0,\ i = 1,\dots,n\}$ and $\Phi(x) = \min_{y \in D(x)} f_0(x,y)$ (4.5), and let $W \subseteq E^x_l$ be a convex set at each point of which this minimum is attained. Then:
--
--   1. $\Phi$ is convex on $W$;
--   2. if $\bar x \in W$ and the Slater condition holds for $f_i(\bar x, y) \le 0$, then for every optimal $y(\bar x) = \bar y$ of the subproblem (4.3)–(4.4):
--      - Kuhn–Tucker multipliers $U = (U_i)$ of (4.3)–(4.4) exist ($U \ge 0$, $U_i f_i(\bar x,\bar y) = 0$, $\bar y$ minimizes $L_U(\bar x,\cdot)$, where $L_U = f_0 + \sum_i U_i f_i$);
--      - for every such $U$, the Lagrange function $L_U$ has a subgradient at $(\bar x,\bar y)$ whose projection on $E^y_m$ vanishes;
--      - for every such subgradient $(g^x_{L_U}(\bar x, y(\bar x)), 0)$,
--   $$
--   g_\Phi(\bar x) = g^x_{L_U}(\bar x, y(\bar x)) \qquad (4.6)
--   $$
--   is a subgradient of $\Phi$ at $\bar x$: $\Phi(x) - \Phi(\bar x) \ge (x - \bar x, g_\Phi(\bar x))$ for all $x \in W$.
--
--   Theorem 4.1 reduces a convex program in $(x,y)$ to the convex minimization of $\Phi$ over $x$, with a subgradient of $\Phi$ read off from the solution and multipliers of the subproblem in $y$; this is the basis of the subgradient decomposition algorithm (steps (a)–(c), p. 96).
--
--   **Formalization Note** The book's "convex on some convex subset $W$ of $E_n$" is read as convexity on every convex set of $x$-values where $\Phi$ is defined. The printed "(3.4)–(4.4)" is read as (4.3)–(4.4). Formula (4.6) is stated, as the book's proof uses it, for a subgradient of $L_U$ whose $y$-projection vanishes; for an arbitrary subgradient of $L_U$ the $x$-projection need not be a subgradient of $\Phi$.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 94, Theorem 4.1; proof pp. 94–95

import Mathlib
import Definitions.Def_ShorNonsmooth_Decomposition_ValueFunction

namespace ShorNonsmooth.Decomposition

/-- Shor (1985), **Theorem 4.1** (p. 94). Let `f₀` and `f_i`, `i = 1, …, n`, be jointly convex functions
of `(x, y)`, and let `W` be a convex set of `x`-values at each of which problem (4.3)–(4.4) has a
solution. Then

1. the value function `Φ` of (4.5) is convex on `W`;
2. if `xbar ∈ W` and the Slater constraint qualification holds for (4.4) at `xbar`, then for every optimal
   `y(xbar) = ybar`: Kuhn–Tucker multipliers `U` of (4.3)–(4.4) exist; for every such `U`, `L_U` has a
   subgradient at `(xbar, ybar)` with null projection on the `y`-space; and the `x`-projection `gx` of every such
   subgradient is a subgradient of `Φ` at `xbar` on `W` (formula (4.6)). -/
theorem value_function_convex_and_subgradient {l m n : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hf₀ : JointlyConvex f₀) (hf : ∀ i, JointlyConvex (f i))
    (W : Set (EuclideanSpace ℝ (Fin l))) (hW : Convex ℝ W)
    (hWmin : ∀ x ∈ W, MinAttained f₀ f x) :
    ConvexOn ℝ W (valueFn f₀ f) ∧
      ∀ xbar ∈ W, SlaterAt f xbar → ∀ ybar, IsOptimalY f₀ f xbar ybar →
        (∃ U : Fin n → ℝ, IsKuhnTuckerMultiplier f₀ f xbar ybar U) ∧
        ∀ U : Fin n → ℝ, IsKuhnTuckerMultiplier f₀ f xbar ybar U →
          (∃ gx, IsJointSubgradient (lagrangian f₀ f U) xbar ybar gx 0) ∧
          ∀ gx, IsJointSubgradient (lagrangian f₀ f U) xbar ybar gx 0 →
            IsSubgradientOn (valueFn f₀ f) W xbar gx := by sorry

end ShorNonsmooth.Decomposition
