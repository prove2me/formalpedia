-- Prove2me | Theorems.Thm_QueueingFundamentals_MG1_queue_wait_lst
-- name    : QueueingFundamentals.MG1.queue_wait_lst
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T09:39:19.385782+00:00
-- url     : https://prove2.me/theorems/065fc791-8f41-46e9-9ca7-5e1b4f8b7424
-- title:
--   Eq. (5.34) — the Pollaczek–Khintchine transform of the line wait
-- statement:
--   Under the hypotheses of (5.33), let also $W_q$ be a probability distribution on $[0,\infty)$ (the FCFS line-wait distribution) with $W = W_q * B$, the convolution expressing $T = T_q + S$ with $T_q$ and $S$ independent. Then for every real $s > 0$,
--
--   $$
--   W_q^*(s) = \frac{(1-\rho)\,s}{s - \lambda[1 - B^*(s)]} .
--   $$
--
--   Expanding this as a geometric series gives the book's representation (5.35) of $W_q$ through the residual-service distribution.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.237, Eq. (5.34)

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_embeddedChain
import Definitions.Def_QueueingFundamentals_MG1_transforms

namespace QueueingFundamentals.MG1

open MeasureTheory

/-- Eq. (5.34), p.237. Under the hypotheses of (5.33), let `W_q` be a probability distribution on
`[0, ∞)` (the FCFS line-wait distribution) with `W = W_q * B`, the convolution expressing
`T = T_q + S` with `T_q` and `S` independent. Then for every real `s > 0`,
`W_q*(s) = (1 - ρ) s / (s - λ[1 - B*(s)])`. -/
theorem queue_wait_lst (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (hint : Integrable (fun t : ℝ => t) B) (hρ : utilization lam B < 1)
    (π : ℕ → ℝ) (hπ : IsStationaryDist (transitionMatrix lam B) π)
    (W : Measure ℝ) [IsProbabilityMeasure W] (hW : W (Set.Iio 0) = 0)
    (hπW : ∀ n : ℕ, π n = ∫ t, (lam * t) ^ n * Real.exp (-(lam * t)) / (Nat.factorial n : ℝ) ∂W)
    (Wq : Measure ℝ) [IsProbabilityMeasure Wq] (hWq : Wq (Set.Iio 0) = 0)
    (hconv : W = Wq.conv B) :
    ∀ s : ℝ, 0 < s →
      lst Wq s = (1 - (utilization lam B : ℂ)) * s / (s - lam * (1 - lst B s)) := by sorry

end QueueingFundamentals.MG1
