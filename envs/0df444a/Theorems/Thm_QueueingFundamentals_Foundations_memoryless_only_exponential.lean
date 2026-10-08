-- Prove2me | Theorems.Thm_QueueingFundamentals_Foundations_memoryless_only_exponential
-- name    : QueueingFundamentals.Foundations.memoryless_only_exponential
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T06:35:33.788989+00:00
-- url     : https://prove2.me/theorems/fec9ab62-8f04-4edc-a81f-597ec4fe4c01
-- title:
--   The exponential is the only continuous memoryless distribution (p.21)
-- statement:
--   Let $T$ be a random variable with values in $[0,\infty)$ almost surely, whose distribution is continuous ($\Pr\{T=a\}=0$ for every real $a$). Suppose $T$ has the memoryless property (1.17): for all $0\le t_0\le t_1$,
--   $$\Pr\{T\le t_1\mid T\ge t_0\}=\Pr\{0\le T\le t_1-t_0\}.$$
--   Then there is $\lambda>0$ such that $T$ is exponentially distributed with rate $\lambda$, i.e. $\Pr\{T\le t\}=1-e^{-\lambda t}$ for $t\ge0$.
--
--   Together with (1.17) this characterizes the exponential distribution among continuous distributions on $[0,\infty)$.
--
--   **Formalization Note** "Continuous distribution" is read as a continuous distribution function (no atoms). The conditional probability is Mathlib's `cond`, which is the zero measure when the conditioning event has probability zero; the hypothesis then forces that case not to occur.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.21, characterization of the exponential distribution following Eq. (1.17) (unnumbered)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace QueueingFundamentals.Foundations

/-- p.21: the exponential distribution is the only continuous distribution on `[0, ∞)` with the
memoryless property (1.17). -/
theorem memoryless_only_exponential {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (T : Ω → ℝ) (hTm : Measurable T)
    (hcont : ∀ a : ℝ, μ {ω | T ω = a} = 0) (hnonneg : μ {ω | T ω < 0} = 0)
    (hmem : ∀ t₀ t₁ : ℝ, 0 ≤ t₀ → t₀ ≤ t₁ →
      cond μ {ω | t₀ ≤ T ω} {ω | T ω ≤ t₁} = μ {ω | 0 ≤ T ω ∧ T ω ≤ t₁ - t₀}) :
    ∃ lam : ℝ, 0 < lam ∧ μ.map T = expMeasure lam := by sorry

end QueueingFundamentals.Foundations
