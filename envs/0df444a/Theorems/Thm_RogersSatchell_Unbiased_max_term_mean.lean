-- Prove2me | Theorems.Thm_RogersSatchell_Unbiased_max_term_mean
-- name    : RogersSatchell.Unbiased.max_term_mean
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:45.757458+00:00
-- url     : https://prove2.me/theorems/4576a5b5-0ab3-4dbc-84a7-ca02023f3f97
-- title:
--   Section 2, p. 505 — E S_t(S_t − X_t) = σ²t/2 for every drift c and every t ≥ 0
-- statement:
--   Let $B$ be a standard Brownian motion on a probability space with every sample path continuous, let $c\in\mathbb R$ and $\sigma\ge 0$, and let $X_t=\sigma B_t+ct$ with running maximum $S_t=\sup_{0\le u\le t}X_u$. Then for every $t\ge0$ the random variable $S_t(S_t-X_t)$ is integrable and
--   $$E\big[S_t(S_t-X_t)\big]=\frac{\sigma^2t}{2}.$$
--
--   This is the half of display (3) that involves the high and the close; its right-hand side does not depend on the drift $c$.
--
--   **Formalization Note** Integrability is asserted together with the value of the Bochner integral. $\sigma=0$ is allowed (both sides are $0$).
-- source:
--   Rogers and Satchell, Estimating variance from high, low and closing prices, Ann. Appl. Probab. 1 (1991), Section 2, p. 505

import Mathlib
import Definitions.Def_RogersSatchell_Unbiased_Process

open MeasureTheory ProbabilityTheory NNReal

namespace RogersSatchell.Unbiased

/-- Rogers–Satchell 1991, §2, p. 505: `E S_t(S_t − X_t) = σ²t/2` for every drift `c`, every `σ ≥ 0`
and every time `t ≥ 0`. -/
theorem max_term_mean
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hcont : ∀ ω, Continuous fun t => B t ω)
    (c σ : ℝ) (hσ : 0 ≤ σ) (t : ℝ≥0) :
    Integrable (fun ω => runMax σ c B t ω * (runMax σ c B t ω - logPrice σ c B t ω)) P ∧
    ∫ ω, runMax σ c B t ω * (runMax σ c B t ω - logPrice σ c B t ω) ∂P = σ ^ 2 * t / 2 := by sorry

end RogersSatchell.Unbiased
