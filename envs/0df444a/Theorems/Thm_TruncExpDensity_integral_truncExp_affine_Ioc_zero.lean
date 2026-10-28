-- Prove2me | Theorems.Thm_TruncExpDensity_integral_truncExp_affine_Ioc_zero
-- name    : TruncExpDensity.integral_truncExp_affine_Ioc_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T06:05:50.788522+00:00
-- url     : https://prove2.me/theorems/1bb1748b-9d04-41ef-b402-6f107469eac1
-- title:
--   $\int_0^{\eta}$ of a truncated exponential against an affine weight
-- statement:
--   Let $\eta \ge 0$, $\delta \ge 0$ and $k, u, v \in \mathbb{R}$, and let $h(t) = k\,e^{t}\,\mathbf 1\{0 < t \le \delta\}$ be the exponential truncated to $(0,\delta]$. Then
--
--   $$
--   \int_0^{\eta} h(t)\,(ut+v)\,dt \;=\; k\Big(e^{\min(\eta,\delta)}\big(u\min(\eta,\delta)+v-u\big) \;-\; (v-u)\Big).
--   $$
--
--   The truncation point enters only through $\min(\eta,\delta)$, and no hypothesis relating $\eta$ to $\delta$ is needed: when $\eta \le \delta$ the density is not truncated on $(0,\eta]$ and the right-hand side is the plain antiderivative, while for $\eta > \delta$ the integral saturates at $\delta$.
--
--   In the analysis of random $\alpha$-schedules this is the computation behind the bound on the delay a job suffers from jobs released before its own $\alpha$-point: the weight is $u = 1$, $v = 1-\eta$, i.e. $1 + \alpha - \eta$. Taking $u = 0, v = 1$ gives the normalization $\int_0^1 h = 1$ and taking $u = 1, v = 0$ gives the mean $\mathbb{E}[\alpha]$, so one result covers all three uses.
--
--   **Formalization Note** $\int_0^{\eta}$ is the interval integral `intervalIntegral`; the statement is for arbitrary real $k$, so no positivity is assumed.
-- source:
--   Lower-interval density computation in Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002) 165-192, DOI 10.1137/S089548019936223X, proof of Lemma 3.6 (p. 183) and proof of Lemma 3.11 (p. 185); stated here for general $\eta, \delta, k$ and a general affine weight.

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
open Set MeasureTheory

theorem TruncExpDensity.integral_truncExp_affine_Ioc_zero (η δ k : ℝ) (hη : 0 ≤ η) (hδ : 0 ≤ δ) (u v : ℝ) :
    (∫ t in (0 : ℝ)..η,(if 0 < t ∧ t ≤ δ then k*Real.exp t else 0)*(u*t+v))=
      k*(Real.exp (min η δ)*(u*min η δ+v-u)-(v-u)) := by sorry
