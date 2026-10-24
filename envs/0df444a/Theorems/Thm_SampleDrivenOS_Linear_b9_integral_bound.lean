-- Prove2me | Theorems.Thm_SampleDrivenOS_Linear_b9_integral_bound
-- name    : SampleDrivenOS.Linear.b9_integral_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:24.272115+00:00
-- url     : https://prove2.me/theorems/57bc8665-13c3-4e38-804c-63a1e443c437
-- title:
--   B.9, p. 37 — the integral bound through the defining equation of $\alpha^*$
-- statement:
--   Let $\alpha^*\in(0,1)$ satisfy
--   $$\int_0^1\frac{dy}{y(1-\ln y)+1/\alpha^*-1}=1,$$
--   and let $p\in(0,1)$. Then
--   $$\frac1p\int_0^1\frac{dy}{\tfrac1{p\alpha^*}-1+y(1-p\ln y)}\le\frac1p-\frac{1-p}{p}\Bigl(\frac1{p\alpha^*}-\frac1e\Bigr)\ln\left(\frac{\tfrac1{p\alpha^*}+\tfrac pe}{\tfrac1{p\alpha^*}+\tfrac pe-1}\right).$$
--
--   This is the only step of the proof of Theorem 9 where the defining equation of $\alpha^*$ enters; it turns the integral of the previous step into a closed-form expression.
--
--   **Formalization Note** $\alpha^*$ is any $s$ with `IsAlphaStar s` (its existence and uniqueness are posed separately, as `CorreaThreshold.Adaptive.beta_star_existsUnique` with $\beta=1/\alpha^*$). The paper's chain has an intermediate member and two inequalities; only the first and last members are stated. $e=\exp 1$. The argument of the logarithm exceeds $1$ because $1/(p\alpha^*)+p/e-1>0$. The integrand is continuous on $[0,1]$ with Lean's value at $y=0$ equal to its limit.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 37, B.9 (Proof of Theorem 9), first display, first and last members

import Mathlib
import Definitions.Def_SampleDrivenOS_Linear_Setting

namespace SampleDrivenOS.Linear

theorem b9_integral_bound (s : ℝ) (hs : SampleDrivenOS.Limit.IsAlphaStar s) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    1 / p * (∫ y in (0 : ℝ)..1, 1 / (1 / (p * s) - 1 + y * (1 - p * Real.log y))) ≤
      1 / p - (1 - p) / p * ((1 / (p * s) - 1 / Real.exp 1) *
        Real.log ((1 / (p * s) + p / Real.exp 1) / (1 / (p * s) + p / Real.exp 1 - 1))) := by sorry

end SampleDrivenOS.Linear
