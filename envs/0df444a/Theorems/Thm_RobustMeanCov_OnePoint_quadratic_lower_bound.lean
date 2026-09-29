-- Prove2me | Theorems.Thm_RobustMeanCov_OnePoint_quadratic_lower_bound
-- name    : RobustMeanCov.OnePoint.quadratic_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:44:50.430285+00:00
-- url     : https://prove2.me/theorems/1dcbb71e-2007-4f64-bace-02f2de391cdf
-- title:
--   Proposition 3 — a supporting quadratic bounds the robust objective from below
-- statement:
--   Let $u:\mathbb R\to\mathbb R$, $m,s\in\mathbb R$, and let $\nu\in\mathbb M_{(m,s^2)}$ be a probability law with mean $m$ and variance $s^2$ under which $u$ is integrable. If $(A,B,C)$ lies in
--
--   $$
--   \mathcal Q=\{(A,B,C):\ Ay^2+By+C\le u(y)\ \text{for all } y\in\mathbb R\},
--   $$
--
--   then
--
--   $$
--   A(m^2+s^2)+Bm+C\ \le\ \int u\,d\nu .
--   $$
--
--   Since every value $E[u(r)]$, $r\sim(m,s^2)$, is at least every value $A(m^2+s^2)+Bm+C$, $(A,B,C)\in\mathcal Q$, this is Proposition 3: $\min_{r}E[u(r)]\ge\max_{\mathcal Q}A(\mu_x^2+\sigma_x^2)+B\mu_x+C$ in the wide sense of $\inf$ and $\sup$.
--
--   **Formalization Note** The "min $\ge$ max" of the paper is stated as "every value $\ge$ every value", which is equivalent and avoids real infima and suprema. Integrability of $u$ under $\nu$ is assumed, so that the integral is the expectation.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, p. 101, §3, Proposition 3 and the sentence preceding it

import Mathlib
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory

namespace RobustMeanCov.OnePoint

theorem quadratic_lower_bound (u : ℝ → ℝ) (m s : ℝ) (ν : Measure ℝ)
    (hν : ν ∈ RobustMeanCov.Shared.MeanVarClass m (s ^ 2)) (hint : Integrable u ν) (A B C : ℝ)
    (hq : ∀ y : ℝ, A * y ^ 2 + B * y + C ≤ u y) :
    A * (m ^ 2 + s ^ 2) + B * m + C ≤ ∫ y, u y ∂ν := by sorry

end RobustMeanCov.OnePoint
