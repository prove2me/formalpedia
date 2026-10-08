-- Prove2me | Theorems.Thm_QueueingFundamentals_MG1_wait_lst
-- name    : QueueingFundamentals.MG1.wait_lst
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T09:39:16.662119+00:00
-- url     : https://prove2.me/theorems/8528eff9-e89f-442f-a0d5-1ed2788eac18
-- title:
--   Eqs. (5.29) and (5.33) — the Pollaczek–Khintchine transform of the system wait
-- statement:
--   Let $\lambda > 0$, let $B$ be a service-time distribution on $[0,\infty)$ with finite mean, $\rho = \lambda\,\mathrm E[S] < 1$, and let $\pi$ be the stationary distribution of the M/G/1 departure-point chain. Let $W$ be a probability distribution on $[0,\infty)$ (the FCFS system-wait distribution) such that
--
--   $$
--   \pi_n = \frac{1}{n!}\int_0^\infty (\lambda t)^n e^{-\lambda t}\,dW(t) \qquad (n \ge 0).
--   $$
--
--   Then:
--
--   1. $\Pi(z) = W^*[\lambda(1-z)]$ for every complex $|z| \le 1$;
--   2. for every real $s > 0$,
--
--   $$
--   W^*(s) = \frac{(1-\rho)\,s\,B^*(s)}{s - \lambda[1 - B^*(s)]} .
--   $$
--
--   The second formula expresses the transform of the waiting-time distribution through the service-time transform alone.
--
--   **Formalization Note** The relation between $\pi$ and $W$ is the book's description of FCFS (p.235: the system size at a departure equals the number of arrivals during that customer's system wait); it is taken as a hypothesis, as the book takes it. The book gives no domain for $s$; the statement uses real $s > 0$.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.235–237, Eqs. (5.29) and (5.33)

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_embeddedChain
import Definitions.Def_QueueingFundamentals_MG1_transforms

namespace QueueingFundamentals.MG1

open MeasureTheory

/-- Eqs. (5.29) and (5.33), pp.235–237. Let `ρ = λ E[S] < 1`, let `π` be the stationary
departure-point distribution, and let `W` be a probability distribution on `[0, ∞)` (the FCFS
system-wait distribution) with `π_n = (1/n!) ∫_0^∞ (λt)^n e^{-λt} dW(t)` for all `n` (p.235).
Then `Π(z) = W*[λ(1 - z)]` for `|z| ≤ 1` (5.29), and for every real `s > 0`,
`W*(s) = (1 - ρ) s B*(s) / (s - λ[1 - B*(s)])` (5.33). -/
theorem wait_lst (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (hint : Integrable (fun t : ℝ => t) B) (hρ : utilization lam B < 1)
    (π : ℕ → ℝ) (hπ : IsStationaryDist (transitionMatrix lam B) π)
    (W : Measure ℝ) [IsProbabilityMeasure W] (hW : W (Set.Iio 0) = 0)
    (hπW : ∀ n : ℕ, π n = ∫ t, (lam * t) ^ n * Real.exp (-(lam * t)) / (Nat.factorial n : ℝ) ∂W) :
    (∀ z : ℂ, ‖z‖ ≤ 1 → pgf π z = lst W ((lam : ℂ) * (1 - z))) ∧
    ∀ s : ℝ, 0 < s →
      lst W s = (1 - (utilization lam B : ℂ)) * s * lst B s / (s - lam * (1 - lst B s)) := by sorry

end QueueingFundamentals.MG1
