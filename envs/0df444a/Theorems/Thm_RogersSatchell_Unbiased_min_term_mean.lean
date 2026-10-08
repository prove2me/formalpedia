-- Prove2me | Theorems.Thm_RogersSatchell_Unbiased_min_term_mean
-- name    : RogersSatchell.Unbiased.min_term_mean
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:53.516977+00:00
-- url     : https://prove2.me/theorems/840eb37a-7819-4bf8-9881-9e6ef0645199
-- title:
--   Section 2, p. 505 — E I_t(I_t − X_t) = σ²t/2 for every drift c and every t ≥ 0
-- statement:
--   Let $B$ be a standard Brownian motion on a probability space with every sample path continuous, let $c\in\mathbb R$ and $\sigma\ge 0$, and let $X_t=\sigma B_t+ct$ with running minimum $I_t=\inf_{0\le u\le t}X_u$. Then for every $t\ge0$ the random variable $I_t(I_t-X_t)$ is integrable and
--   $$E\big[I_t(I_t-X_t)\big]=\frac{\sigma^2t}{2}.$$
--
--   The paper obtains this by "a symmetric argument" from the statement for the running maximum; it is the half of display (3) that involves the low and the close.
--
--   **Formalization Note** Integrability is asserted together with the value of the Bochner integral. $\sigma=0$ is allowed.
-- source:
--   Rogers and Satchell, Estimating variance from high, low and closing prices, Ann. Appl. Probab. 1 (1991), Section 2, p. 505

import Mathlib
import Definitions.Def_RogersSatchell_Unbiased_Process

open MeasureTheory ProbabilityTheory NNReal

namespace RogersSatchell.Unbiased

/-- Rogers–Satchell 1991, §2, p. 505 ("a symmetric argument"): `E I_t(I_t − X_t) = σ²t/2` for every
drift `c`, every `σ ≥ 0` and every time `t ≥ 0`. -/
theorem min_term_mean
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hcont : ∀ ω, Continuous fun t => B t ω)
    (c σ : ℝ) (hσ : 0 ≤ σ) (t : ℝ≥0) :
    Integrable (fun ω => runMin σ c B t ω * (runMin σ c B t ω - logPrice σ c B t ω)) P ∧
    ∫ ω, runMin σ c B t ω * (runMin σ c B t ω - logPrice σ c B t ω) ∂P = σ ^ 2 * t / 2 := by sorry

end RogersSatchell.Unbiased
