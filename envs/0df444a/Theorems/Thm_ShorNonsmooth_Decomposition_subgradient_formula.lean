-- Prove2me | Theorems.Thm_ShorNonsmooth_Decomposition_subgradient_formula
-- name    : ShorNonsmooth.Decomposition.subgradient_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T16:23:58.790121+00:00
-- url     : https://prove2.me/theorems/f9c887b8-417f-410b-929d-8b7923caa517
-- title:
--   Theorem 4.1, formula (4.6) — the $x$-projection of a subgradient of $L_U$ with null $y$-projection is a subgradient of $\Phi$
-- statement:
--   Let $f_0$ and $f_i$, $i = 1,\dots,n$, be jointly convex, let $W$ be a convex set of $x$-values at which the minimum in (4.5) is attained, let $\bar x \in W$, let $\bar y$ be an optimal solution of the subproblem at $\bar x$, and let $U$ be Kuhn–Tucker multipliers at $\bar x$ relative to $\bar y$. If $(g^x, 0)$ is a subgradient of $L_U$ at $(\bar x,\bar y)$, then
--   $$
--   \Phi(x) - \Phi(\bar x) \ge (x - \bar x,\ g^x) \qquad \text{for all } x \in W,
--   $$
--   so $g_\Phi(\bar x) = g^x_{L_U}(\bar x, y(\bar x))$ is a subgradient of $\Phi$ at $\bar x$ (formula (4.6)).
--
--   This is the step that turns decomposition into a subgradient method: the subproblem's solution and multipliers yield a subgradient of the master function $\Phi$.
--
--   **Formalization Note** The book derives this inequality in a neighbourhood of $\bar x$ where the Slater condition persists; the statement here is on all of $W$, which the same estimate gives. The Slater condition is not a hypothesis of this step: it only serves to guarantee that multipliers exist (the preceding milestone).
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 95, proof of Theorem 4.1, final display; formula (4.6), p. 94

import Mathlib
import Definitions.Def_ShorNonsmooth_Decomposition_ValueFunction

namespace ShorNonsmooth.Decomposition

/-- Shor (1985), proof of Theorem 4.1, p. 95 (last display): let `f₀`, `f_i` be jointly convex, `W` a
convex set on which the minimum in (4.5) is attained, `xbar ∈ W`, `ybar` an optimal value of `y` in
(4.3)–(4.4) at `xbar`, and `U` Kuhn–Tucker multipliers at `xbar`. If `(gx, 0)` is a subgradient of `L_U`
at `(xbar, ybar)` (its projection on the `y`-space vanishes), then `gx` is a subgradient of `Φ` at
`xbar` on `W`: `Φ(x) − Φ(xbar) ≥ (x − xbar, gx)` for all `x ∈ W` — formula (4.6). -/
theorem subgradient_formula {l m n : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hf₀ : JointlyConvex f₀) (hf : ∀ i, JointlyConvex (f i))
    (W : Set (EuclideanSpace ℝ (Fin l))) (hW : Convex ℝ W)
    (hWmin : ∀ x ∈ W, MinAttained f₀ f x)
    (xbar : EuclideanSpace ℝ (Fin l)) (hxbar : xbar ∈ W)
    (ybar : EuclideanSpace ℝ (Fin m)) (hybar : IsOptimalY f₀ f xbar ybar)
    (U : Fin n → ℝ) (hU : IsKuhnTuckerMultiplier f₀ f xbar ybar U)
    (gx : EuclideanSpace ℝ (Fin l)) (hgx : IsJointSubgradient (lagrangian f₀ f U) xbar ybar gx 0) :
    IsSubgradientOn (valueFn f₀ f) W xbar gx := by sorry

end ShorNonsmooth.Decomposition
