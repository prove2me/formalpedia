-- Prove2me | Theorems.Thm_QueueingFundamentals_Bounds_r0_lower_bound
-- name    : QueueingFundamentals.Bounds.r0_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T09:34:17.508101+00:00
-- url     : https://prove2.me/theorems/41ae8fee-7163-4746-b5a1-ded63bfc2574
-- title:
--   Eqs. (7.15)–(7.16) — the root $r_0$ of $f(z) = z - \int_{-z}^\infty [1 - U(t)]\,dt$ and $W_q \ge r_0$
-- statement:
--   Consider a G/G/1 queue whose interarrival time $T$ and service time $S$ are nonnegative, have finite second moments, and satisfy $E[T] = 1/\lambda$ and $E[S] = 1/\mu$ with $\lambda, \mu > 0$ and $\rho = \lambda/\mu < 1$. Let $\nu$ be a stationary law of the line delay under Lindley's recursion (7.1). Let $U(t)$ be the CDF of $U = S - T$ ($S$, $T$ independent), and set
--   $$
--   f_1(z) = \int_{-z}^{\infty} [1 - U(t)]\,dt, \qquad f(z) = z - f_1(z).
--   $$
--
--   Then:
--   1. $f$ has exactly one nonnegative root $r_0$.
--   2. The mean stationary line delay $W_q$ is finite, and
--   $$
--   W_q \ge f_1(W_q) = \int_{-W_q}^{\infty} [1 - U(t)]\,dt. \qquad (7.16)
--   $$
--   3. For every real $z$,
--   $$
--   f_1(z) \begin{cases} > z & (z < r_0), \\ \le z & (z \ge r_0), \end{cases} \qquad (7.15)
--   $$
--   and $W_q \ge r_0$.
--
--   This lower bound uses the full distributions of $S$ and $T$, not only their first two moments.
--
--   **Formalization Note** The conclusions about $r_0$ are stated for every nonnegative root of $f$; item 1 says there is exactly one. (7.15) is stated for all real $z$. For $z < 0$ it holds because $f_1 \ge 0$.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.334–336, f(z), Eqs. (7.15), (7.16) and W_q ≥ r_0

import Mathlib
import Definitions.Def_QueueingFundamentals_Bounds_GG1

namespace QueueingFundamentals.Bounds

open MeasureTheory ProbabilityTheory Filter Topology

/-- pp.334–336, Eqs. (7.15)–(7.16). For a stationary G/G/1 queue with `ρ < 1`:
`f(z) = z − ∫_{−z}^{∞} [1 − U(t)] dt` has a unique nonnegative root `r₀`; the stationary line delay
has finite mean with `W_q ≥ f₁(W_q)` (7.16); and for that root, `f₁(z) > z` for `z < r₀` and
`f₁(z) ≤ z` for `z ≥ r₀` (7.15), and `W_q ≥ r₀`. -/
theorem r0_lower_bound
    {A B ν : Measure ℝ} {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hin : IsGG1Input A B lam mu) (hrho : lam / mu < 1) (hν : IsStationaryWaitLaw A B ν) :
    (∃! r : ℝ, 0 ≤ r ∧ rootFun A B r = 0) ∧
    Integrable (fun w : ℝ => w) ν ∧
    f1 A B (meanWait ν) ≤ meanWait ν ∧
    ∀ r : ℝ, 0 ≤ r → rootFun A B r = 0 →
      (∀ z : ℝ, (z < r → z < f1 A B z) ∧ (r ≤ z → f1 A B z ≤ z)) ∧ r ≤ meanWait ν := by sorry

end QueueingFundamentals.Bounds
