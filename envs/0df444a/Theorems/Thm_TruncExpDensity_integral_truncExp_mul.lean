-- Prove2me | Theorems.Thm_TruncExpDensity_integral_truncExp_mul
-- name    : TruncExpDensity.integral_truncExp_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T06:05:51.737221+00:00
-- url     : https://prove2.me/theorems/0fd73639-78ff-483c-9490-575b6b2f8bf9
-- title:
--   A truncated exponential integrand shortens the interval of integration
-- statement:
--   Fix $\delta, k \in \mathbb{R}$ and let
--
--   $$
--   h(t) \;=\; \begin{cases} k\,e^{t}, & 0 < t \le \delta,\\[2pt] 0, & \text{otherwise,}\end{cases}
--   $$
--
--   be the exponential truncated to $(0,\delta]$. Then for all $0 \le a \le b$ and every function $H : \mathbb{R} \to \mathbb{R}$,
--
--   $$
--   \int_a^b h(t)\,H(t)\,dt \;=\; \int_a^{\min(b,\,\delta)} k\,e^{t}\,H(t)\,dt .
--   $$
--
--   Because the lower endpoint satisfies $a \ge 0$, the indicator $\mathbf 1\{0 < t \le \delta\}$ can only cut the interval at its upper end, so integrating the truncated density against an arbitrary weight is the same as integrating the untruncated $k\,e^{t}H(t)$ up to $\min(b,\delta)$.
--
--   Together with the closed form for $\int k e^{t}(ut+v)\,dt$ this reduces every moment of a truncated exponential density to an evaluation at two endpoints, with no case distinction left inside the integral. The weight $H$ is arbitrary, so the same statement serves the first-moment, the delay and the normalization computations.
--
--   **Formalization Note** Both integrals are over `Set.Ioc`; the proof rewrites the integrand as the indicator of `Set.Ioc 0 δ` and intersects the restricted measures.
-- source:
--   Restriction step in the density computations of Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002) 165-192, DOI 10.1137/S089548019936223X, proof of Lemma 3.6 (p. 183) and proof of Lemma 3.11 (p. 185); stated here for a general weight $H$ and general $\delta, k$.

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
open Set MeasureTheory

theorem TruncExpDensity.integral_truncExp_mul (a b δ k : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (H : ℝ → ℝ) :
    (∫ t in Set.Ioc a b,(if 0 < t ∧ t ≤ δ then k*Real.exp t else 0)*H t)=
      ∫ t in Set.Ioc a (min b δ),k*Real.exp t*H t := by sorry
