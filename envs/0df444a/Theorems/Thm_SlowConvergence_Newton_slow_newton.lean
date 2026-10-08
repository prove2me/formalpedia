-- Prove2me | Theorems.Thm_SlowConvergence_Newton_slow_newton
-- name    : SlowConvergence.Newton.slow_newton
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:30.686844+00:00
-- url     : https://prove2.me/theorems/706b0662-0827-4c6c-98ec-74b46e44b103
-- title:
--   §3 and §6 — Newton's method can need $\lfloor \varepsilon^{-(2-\tau)} \rfloor$ iterations to reach $\|g\| \le \varepsilon$
-- statement:
--   Let $0 < \tau < 1$. There exist a function $f : \mathbb R^2 \to \mathbb R$ and a sequence $(x_k)_{k \ge 0}$ in $\mathbb R^2$ with the following properties. Write $g(x) = \nabla f(x)$ and $H(x) = \nabla^2 f(x)$.
--
--   1. $f$ is twice continuously differentiable on $\mathbb R^2$, bounded below, and its Hessian is bounded: $\sup_y \|H(y)\| < \infty$.
--   2. $(x_k)$ is a run of Newton's method on $f$ from $x_0 = 0$: for every $k$, $H(x_k)$ is positive definite and $H(x_k)(x_{k+1} - x_k) = -g(x_k)$, so $x_{k+1}$ is the exact minimizer of the quadratic model (1.2).
--   3. The Hessian is Lipschitz continuous along the path, with one constant: there is $L$ such that $\|H(y) - H(z)\| \le L\|y - z\|$ whenever $y, z$ lie on the same segment $[x_k, x_{k+1}]$.
--   4. Each step achieves exactly the model value (3.8):
--   $$f(x_{k+1}) = f(x_k) + g(x_k)^T(x_{k+1}-x_k) + \tfrac12 (x_{k+1}-x_k)^T H(x_k)(x_{k+1}-x_k).$$
--   5. The gradients decay slowly, (2.3): for every $k \ge 0$,
--   $$\|g(x_k)\| \;\ge\; \Big(\frac1{k+1}\Big)^{\frac1{2-\tau}} .$$
--   6. Consequently, for every $\varepsilon \in (0,1)$, if $\|g(x_k)\| \le \varepsilon$ then
--   $$k + 1 \;\ge\; \Big\lfloor \frac{1}{\varepsilon^{2-\tau}} \Big\rfloor ,$$
--   i.e. Newton's method needs at least $\lfloor \varepsilon^{-(2-\tau)} \rfloor$ iterates (function evaluations) $x_0, \dots, x_k$ to produce a gradient of norm at most $\varepsilon$.
--
--   Since $\tau$ is arbitrary, the worst-case iteration count of Newton's method on twice continuously differentiable functions with bounded Hessians that are Lipschitz along the path is not better than $O(\varepsilon^{-2+\tau})$ for any $\tau > 0$: Newton's method may be as slow as steepest descent. Property 4 makes the conclusion apply also when Newton's method is embedded in a trust-region or linesearch globalization, since every unit step is then accepted.
--
--   **Formalization Note** The paper states the result "for any $\tau > 0$"; the construction needs $\tau < 1$, and for $\varepsilon < 1$ the cases $\tau < 1$ imply the iteration bound for every $\tau > 0$. The count is posed for the iterates $x_0, \dots, x_k$ ($k + 1$ of them): as printed, "at least $\lfloor 1/\varepsilon^{2-\tau}\rfloor$ iterations" is off by one. The paper builds $f$ on the nonnegative quadrant and remarks that it extends smoothly; here $f$ is required on all of $\mathbb R^2$. Boundedness of the Hessian is required on all of $\mathbb R^2$, which is stronger than AS.1 ("along each segment"); the Lipschitz constant is uniform in $k$. The plane is `EuclideanSpace ℝ (Fin 2)`, $g$ is `gradient f`, $H$ is `fderiv ℝ (gradient f)` and $\|\cdot\|$ on operators is the operator norm.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, pp. 6–9, §3 (the f_2 example, AS.1 and (3.1)–(3.8)); pp. 15–16, §6; (1.2), p. 1; (2.3), p. 3

import Mathlib

open scoped RealInnerProductSpace

namespace SlowConvergence.Newton

/-- Cartis, Gould & Toint, *On the complexity of steepest descent, Newton's and regularized Newton's
methods for nonconvex unconstrained optimization*, preprint 15 Oct 2009, §3, pp. 6–9 (the `f_2` example)
and §6, pp. 15–16: Newton's method can need `⌊ε^{−(2−τ)}⌋` iterations to reach `‖g‖ ≤ ε`.

For every `τ ∈ (0, 1)` there is a function `f : ℝ² → ℝ` that is twice continuously differentiable,
bounded below, with bounded Hessian, and a run `x_0 = 0, x_1, …` of Newton's method on `f` (at every
iterate the Hessian `H(x_k)` is positive definite and `H(x_k)(x_{k+1} − x_k) = −∇f(x_k)`, i.e. the unit
Newton step minimizing the quadratic model (1.2)), such that
* the Hessian is Lipschitz continuous along every segment `[x_k, x_{k+1}]`, with one constant for all `k`;
* (3.8) `f(x_{k+1}) = m_k(x_{k+1})`, the value of the quadratic model (1.2) at the new iterate;
* (2.3) `‖∇f(x_k)‖ ≥ (1/(k+1))^{1/(2−τ)}` for all `k ≥ 0`;
* for every `ε ∈ (0, 1)`, an iterate `x_k` with `‖∇f(x_k)‖ ≤ ε` has `k + 1 ≥ ⌊ε^{−(2−τ)}⌋`, i.e. at least
  `⌊1/ε^{2−τ}⌋` iterates (function evaluations) `x_0, …, x_k` are needed.

Formalization Note: the paper says "for any τ > 0"; the construction needs `τ < 1`, and the `τ < 1`
cases imply the iteration bound for all `τ > 0` when `ε < 1`. The count is `k + 1` (iterates
`x_0, …, x_k`), because as printed ("at least ⌊1/ε^{2−τ}⌋ iterations") it is off by one. The paper
builds `f` on the nonnegative quadrant and says it extends smoothly; here `f` is required on all of `ℝ²`.
Boundedness of the Hessian is required on all of `ℝ²` (AS.1 asks it along the segments). -/
theorem slow_newton (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ,
      ContDiff ℝ 2 f ∧ BddBelow (Set.range f) ∧
      (∃ M : ℝ, ∀ y, ‖fderiv ℝ (gradient f) y‖ ≤ M) ∧
      ∃ x : ℕ → EuclideanSpace ℝ (Fin 2), x 0 = 0 ∧
        (∀ k, (∀ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 → 0 < ⟪fderiv ℝ (gradient f) (x k) v, v⟫) ∧
          fderiv ℝ (gradient f) (x k) (x (k + 1) - x k) = -gradient f (x k)) ∧
        (∃ L : ℝ, ∀ k, ∀ y ∈ segment ℝ (x k) (x (k + 1)), ∀ z ∈ segment ℝ (x k) (x (k + 1)),
          ‖fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) z‖ ≤ L * ‖y - z‖) ∧
        (∀ k, f (x (k + 1)) = f (x k) + ⟪gradient f (x k), x (k + 1) - x k⟫
          + 1 / 2 * ⟪fderiv ℝ (gradient f) (x k) (x (k + 1) - x k), x (k + 1) - x k⟫) ∧
        (∀ k : ℕ, (1 / ((k : ℝ) + 1)) ^ (1 / (2 - τ)) ≤ ‖gradient f (x k)‖) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ k : ℕ, ‖gradient f (x k)‖ ≤ ε →
          (⌊ε ^ (-(2 - τ))⌋₊ : ℝ) ≤ k + 1) := by sorry

end SlowConvergence.Newton
