-- Prove2me | Theorems.Thm_RogersSatchell_Unbiased_variance_bound
-- name    : RogersSatchell.Unbiased.variance_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:46:02.576981+00:00
-- url     : https://prove2.me/theorems/d64f3228-b977-4894-a52f-b4dfc62f1927
-- title:
--   Section 2, p. 506 — EY₁² = EY₂² = σ⁴/2, EY² ≤ 2σ⁴ and var(σ̂²) ≤ σ⁴ for any drift c
-- statement:
--   Let $B$ be a standard Brownian motion with every sample path continuous, $c\in\mathbb R$, $\sigma\ge0$, $X_t=\sigma B_t+ct$ with running maximum $S_t$ and minimum $I_t$ over $[0,t]$. Put
--   $$Y_1=S_1(S_1-X_1),\qquad Y_2=I_1(I_1-X_1),\qquad Y=Y_1+Y_2=\hat\sigma^2.$$
--   Then $Y_1$ and $Y_2$ are square-integrable, and
--
--   1. $E[Y_1^2]=E[Y_2^2]=\sigma^4/2$;
--   2. $E[Y^2]\le 2\sigma^4$;
--   3. $\operatorname{var}(\hat\sigma^2)\le\sigma^4$.
--
--   The bound holds for every drift $c$, whereas the exact variance $0.331\sigma^4$ quoted by the paper is only known for $c=0$.
--
--   **Formalization Note** Square-integrability is `MemLp _ 2`; the variance is Mathlib's `variance` of $\hat\sigma^2$ under $P$.
-- source:
--   Rogers and Satchell, Estimating variance from high, low and closing prices, Ann. Appl. Probab. 1 (1991), Section 2, p. 506

import Mathlib
import Definitions.Def_RogersSatchell_Unbiased_Process

open MeasureTheory ProbabilityTheory NNReal

namespace RogersSatchell.Unbiased

/-- Rogers–Satchell 1991, §2, p. 506: with `Y₁ = S_1(S_1 − X_1)`, `Y₂ = I_1(I_1 − X_1)` and
`Y = Y₁ + Y₂ = σ̂²`: `EY₁² = EY₂² = σ⁴/2`, `EY² ≤ 2σ⁴` and `var(σ̂²) ≤ σ⁴`, for any drift `c`. -/
theorem variance_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hcont : ∀ ω, Continuous fun t => B t ω)
    (c σ : ℝ) (hσ : 0 ≤ σ) :
    MemLp (fun ω => runMax σ c B 1 ω * (runMax σ c B 1 ω - logPrice σ c B 1 ω)) 2 P ∧
    MemLp (fun ω => runMin σ c B 1 ω * (runMin σ c B 1 ω - logPrice σ c B 1 ω)) 2 P ∧
    ∫ ω, (runMax σ c B 1 ω * (runMax σ c B 1 ω - logPrice σ c B 1 ω)) ^ 2 ∂P = σ ^ 4 / 2 ∧
    ∫ ω, (runMin σ c B 1 ω * (runMin σ c B 1 ω - logPrice σ c B 1 ω)) ^ 2 ∂P = σ ^ 4 / 2 ∧
    ∫ ω, (estimator σ c B 1 ω) ^ 2 ∂P ≤ 2 * σ ^ 4 ∧
    variance (estimator σ c B 1) P ≤ σ ^ 4 := by sorry

end RogersSatchell.Unbiased
