-- Prove2me | Theorems.Thm_TruncExpDensity_integral_truncExp_affine_Ioc_one
-- name    : TruncExpDensity.integral_truncExp_affine_Ioc_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T06:05:52.235165+00:00
-- url     : https://prove2.me/theorems/65110d8e-8ef0-4759-8dd9-8b55bc2ac62e
-- title:
--   $\int_{\mu}^{1}$ of a truncated exponential against an affine weight
-- statement:
--   Let $0 \le \mu \le 1$, let $\delta \le 1$ and let $k, u, v \in \mathbb{R}$. With $h(t) = k\,e^{t}\,\mathbf 1\{0 < t \le \delta\}$ the exponential truncated to $(0,\delta]$,
--
--   $$
--   \int_{\mu}^{1} h(t)\,(ut+v)\,dt \;=\;
--   \begin{cases}
--   k\Big(e^{\delta}(u\delta+v-u) - e^{\mu}(u\mu+v-u)\Big), & \mu \le \delta,\\[4pt]
--   0, & \mu > \delta .
--   \end{cases}
--   $$
--
--   The case distinction is genuine rather than cosmetic: once the lower endpoint $\mu$ passes the truncation point $\delta$ the integrand vanishes identically on $(\mu, 1]$, so the integral is $0$ and the closed form above would be the wrong value.
--
--   This is the companion of the $\int_0^{\eta}$ computation. In the analysis of random $\alpha$-schedules it bounds the delay caused by the jobs whose $\alpha$-points lie after a given threshold $\mu$, with weight $1+\alpha$ (take $u=v=1$) or with constant weight $1$ (take $u=0, v=1$).
--
--   **Formalization Note** $\int_{\mu}^{1}$ is the interval integral; the hypothesis $\delta \le 1$ makes $\min(1,\delta) = \delta$, and the branch $\mu > \delta$ is obtained from `Set.Ioc_eq_empty_of_le`.
-- source:
--   Upper-interval density computation in Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002) 165-192, DOI 10.1137/S089548019936223X, proof of Lemma 3.6 (p. 183) and proof of Lemma 3.11 (p. 185); stated here for general $\mu, \delta, k$ and a general affine weight.

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
open Set MeasureTheory

theorem TruncExpDensity.integral_truncExp_affine_Ioc_one (μ δ k : ℝ) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) (hδ1 : δ ≤ 1) (u v : ℝ) :
    (∫ t in μ..1,(if 0 < t ∧ t ≤ δ then k*Real.exp t else 0)*(u*t+v))=
      if μ ≤ δ then k*(Real.exp δ*(u*δ+v-u)-Real.exp μ*(u*μ+v-u)) else 0 := by sorry
