-- Prove2me | Theorems.Thm_TruncExpDensity_integral_exp_affine
-- name    : TruncExpDensity.integral_exp_affine
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T06:05:49.237774+00:00
-- url     : https://prove2.me/theorems/180a6b5c-69bb-47eb-8f35-5a83d1179691
-- title:
--   $\int_a^b k e^{t}(ut+v)\,dt = k\big[e^{t}(ut+v-u)\big]_a^b$
-- statement:
--   Let $a \le b$ be reals and let $k, u, v \in \mathbb{R}$. The integral of an exponential against an affine function has the elementary closed form
--
--   $$
--   \int_a^b k\,e^{t}\,(ut+v)\,dt \;=\; k\Big[e^{t}\,(ut+v-u)\Big]_a^b \;=\; k\big(e^{b}(ub+v-u)\;-\;e^{a}(ua+v-u)\big),
--   $$
--
--   since $\frac{d}{dt}\big(e^{t}(ut+v-u)\big) = e^{t}(ut+v)$.
--
--   This is the only antiderivative needed when a random variable whose law has a truncated exponential density $k\,e^{\alpha}$ on $(0,\delta]$ is integrated against an affine weight. That is exactly the situation in the analysis of random $\alpha$-schedules for single-machine scheduling with release dates, where the weight is $1+\alpha-\eta$ or $1+\alpha$. Keeping it as a separate result lets the density computations proceed without any calculus.
--
--   **Formalization Note** The integral is the Bochner integral over `Set.Ioc a b` with respect to Lebesgue measure. The integrand is continuous, so this coincides with the interval integral $\int_a^b$.
-- source:
--   Elementary antiderivative, isolated from the density computations in Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002) 165-192, DOI 10.1137/S089548019936223X, proof of Lemma 3.6 (p. 183) and proof of Lemma 3.11 (p. 185).

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
open Set MeasureTheory

theorem TruncExpDensity.integral_exp_affine (a b k u v : ℝ) (hab : a ≤ b) :
    (∫ t in Set.Ioc a b,k*Real.exp t*(u*t+v))=
      k*(Real.exp b*(u*b+v-u)-Real.exp a*(u*a+v-u)) := by sorry
