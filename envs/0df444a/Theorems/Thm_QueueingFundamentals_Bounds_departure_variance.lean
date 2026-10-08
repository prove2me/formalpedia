-- Prove2me | Theorems.Thm_QueueingFundamentals_Bounds_departure_variance
-- name    : QueueingFundamentals.Bounds.departure_variance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T09:33:58.028628+00:00
-- url     : https://prove2.me/theorems/148a4379-029b-469d-9776-02c82efca5d6
-- title:
--   Eq. (7.12) — $\mathrm{Var}[D] = 2\sigma_B^2 + \sigma_A^2 - 2W_q(1/\lambda - 1/\mu)$
-- statement:
--   Consider a G/G/1 queue whose interarrival time $T$ and service time $S$ are nonnegative, have finite second moments, and satisfy $E[T] = 1/\lambda$, $E[S] = 1/\mu$, $\sigma_A^2 = \mathrm{Var}[T]$ and $\sigma_B^2 = \mathrm{Var}[S]$, with $\lambda, \mu > 0$ and $\rho = \lambda/\mu < 1$. Let $\nu$ be a stationary law of the line delay under Lindley's recursion (7.1). The interdeparture time is
--   $$
--   D^{(n)} = S^{(n+1)} + X^{(n)}, \qquad X^{(n)} = -\min(0, W_q^{(n)} + S^{(n)} - T^{(n)}),
--   $$
--   where $W_q^{(n)} \sim \nu$, $S^{(n)}$, $T^{(n)}$ and $S^{(n+1)}$ are independent.
--
--   Then $W_q = E[W_q^{(n)}]$ is finite and the interdeparture time $D$ in steady state satisfies
--   $$
--   \mathrm{Var}[D] = 2\sigma_B^2 + \sigma_A^2 - 2W_q\left(\frac{1}{\lambda} - \frac{1}{\mu}\right). \qquad (7.12)
--   $$
--
--   This is the variance of the departure process of a stationary G/G/1 queue. The approximations of §7.3 for queueing networks use it.
--
--   **Formalization Note** $D$ is a function on the product space of $(S^{(n+1)}, W_q^{(n)}, S^{(n)}, T^{(n)})$ with law $B \otimes \nu \otimes B \otimes A$. The variance is Mathlib's `variance`.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.331–332, D^(n) ≡ S^(n+1) + X^(n) and Eq. (7.12)

import Mathlib
import Definitions.Def_QueueingFundamentals_Bounds_GG1

namespace QueueingFundamentals.Bounds

open MeasureTheory ProbabilityTheory Filter Topology

/-- Eq. (7.12), p.332. For a stationary G/G/1 queue with `ρ < 1`, the interdeparture time
`D = S^{(n+1)} + X^{(n)}` (with `S^{(n+1)} ~ B` independent of `(W_q^{(n)}, S^{(n)}, T^{(n)})`)
satisfies `Var[D] = 2σ_B² + σ_A² − 2W_q(1/λ − 1/μ)`. -/
theorem departure_variance
    {A B ν : Measure ℝ} {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hin : IsGG1Input A B lam mu) (hrho : lam / mu < 1) (hν : IsStationaryWaitLaw A B ν) :
    Integrable (fun w : ℝ => w) ν ∧
    variance (fun q : ℝ × (ℝ × ℝ × ℝ) => q.1 + idleX q.2.1 q.2.2.1 q.2.2.2)
        (B.prod (stepLaw ν B A)) =
      2 * serviceVar B + interarrivalVar A - 2 * meanWait ν * (1 / lam - 1 / mu) := by sorry

end QueueingFundamentals.Bounds
