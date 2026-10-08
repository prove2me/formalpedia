-- Prove2me | Theorems.Thm_SlowConvergence_Newton_third_deriv_along_step
-- name    : SlowConvergence.Newton.third_deriv_along_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:39:51.470052+00:00
-- url     : https://prove2.me/theorems/87ec1925-67c4-40d6-b3fb-48ddb21adc3c
-- title:
--   §3, p. 9 — the third derivative of $f_2$ along each step is at most 858
-- statement:
--   Let $0 < \tau < 1$, and let $p_k$, $q_k$, $\mu_k$ and $s_k = (\mu_k, 1)^T$ be as in the example. On the segment $[x_k, x_{k+1}]$, the point $x_k + t s_k$ ($t \in [0,1]$) has first coordinate at offset $t\mu_k$ in the interval of $p_k$ and second coordinate at offset $t$ in the interval of $q_k$, so the third derivative of $f_2$ along the unit direction $s_k/\|s_k\|$ there is
--   $$\frac{1}{\|s_k\|^3}\Big[p_k'''(t\mu_k)\,\mu_k^3 + q_k'''(t)\Big].$$
--   For every $k \ge 0$ and every $t \in [0,1]$,
--   $$\frac{\big|p_k'''(t\mu_k)\,\mu_k^3 + q_k'''(t)\big|}{\|s_k\|^3} \;\le\; 858 .$$
--
--   The paper deduces from this bound, by the mean-value theorem, that $f_2$ has Lipschitz continuous second derivatives on each segment of the piecewise linear path $\bigcup_k [x_k, x_{k+1}]$.
--
--   **Formalization Note** The page writes $p_k'''(t)(s_k)_1^3$ with one letter $t$ for both pieces; the argument of $p_k'''$ is the rescaled offset $t\mu_k$, with $(s_k)_1 = \mu_k$. The page bounds the signed quantity; the absolute value is stated here.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 9, §3

import Mathlib
import Definitions.Def_SlowConvergence_Newton_Data
import Definitions.Def_SlowConvergence_Newton_Pieces

open scoped RealInnerProductSpace

namespace SlowConvergence.Newton

/-- Cartis, Gould & Toint, preprint 15 Oct 2009, §3, p. 9: the third derivative of `f_2` along the
step, in the `k`-th interval, is at most `858`. At the point `x_k + t s_k`, `t ∈ [0, 1]`, of the
segment `[x_k, x_{k+1}]`, the first coordinate lies at offset `t µ_k` in the interval of `p_k` and the
second at offset `t` in the interval of `q_k`, so the third derivative of `f_2` in the unit direction
`s_k/‖s_k‖` is `(p_k'''(t µ_k) µ_k³ + q_k'''(t)) / ‖s_k‖³`. For all `k ≥ 0` and `t ∈ [0, 1]` its absolute
value is at most `858`.

Formalization Note: the page writes `p_k'''(t)(s_k)_1³` with one letter `t` for both pieces; the
argument of `p_k'''` is the rescaled offset `t µ_k` (with `(s_k)_1 = µ_k`). The page's chain bounds the
signed quantity; the absolute value is stated here, which is what Lipschitz continuity needs. -/
theorem third_deriv_along_step (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDeriv 3 (p τ k) (t * mu τ k) * mu τ k ^ 3 + iteratedDeriv 3 (q k) t|
          / ‖sk τ k‖ ^ 3 ≤ 858 := by sorry

end SlowConvergence.Newton
