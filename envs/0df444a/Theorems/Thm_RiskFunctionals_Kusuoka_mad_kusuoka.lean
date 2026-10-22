-- Prove2me | Theorems.Thm_RiskFunctionals_Kusuoka_mad_kusuoka
-- name    : RiskFunctionals.Kusuoka.mad_kusuoka
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:51:50.363802+00:00
-- url     : https://prove2.me/theorems/ddb18d09-796d-47a0-9d27-f3f0cb71234d
-- title:
--   Example 2.46, Eq. (2.41) — Kusuoka representation of $\mathbb E(Y)-\tfrac12\mathbb{M}\mathrm{ad}(Y)$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a non-atomic probability space and $Y$ an integrable random variable. Write $\mathbb{M}\mathrm{ad}(Y)=\mathbb E|Y-\mathbb EY|$ for the mean absolute deviation and $\mathcal P(0,1]$ for the set of probability measures on $(0,1]$. Then
--   $$\mathbb E(Y)-\tfrac12\mathbb{M}\mathrm{ad}(Y)=\inf\Big\{\int_{(0,1]}\mathbb{AV@R}_\alpha(Y)\,dm(\alpha) : m\in\mathcal P(0,1],\ \int_{(0,1)}\frac1v\,dm(v)\le1\Big\}. \tag{2.41}$$
--
--   This makes the abstract Kusuoka representation explicit for the mean-absolute-deviation corrected mean: its dual variables are probability densities, and the admissible mixing measures are exactly the probabilities on $(0,1]$ whose $1/v$-moment on $(0,1)$ is at most one.
--
--   **Formalization Note** The constraint $\int_{(0,1)}\frac1v\,dm(v)\le1$ is a non-negative (possibly infinite) integral, computed with values in $[0,\infty]$ so that a divergent integral violates it. For every admissible $m$ the map $\alpha\mapsto\mathbb{AV@R}_\alpha(Y)$ is $m$-integrable, since $|\mathbb{AV@R}_\alpha(Y)|\le\mathbb E|Y|/\alpha$. The infimum is a greatest lower bound in $\mathbb R$. Non-atomicity is the standing assumption of the section.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 64, Example 2.46, Eq. (2.41)

import Mathlib
import Definitions.Def_RiskFunctionals_Kusuoka_AverageValueAtRisk
import Definitions.Def_RiskFunctionals_Kusuoka_Functionals
open MeasureTheory ProbabilityTheory

namespace RiskFunctionals.Kusuoka

/-- Pflug & Römisch, p. 64, Example 2.46, (2.41): the Kusuoka representation of the
`𝕄ad`-corrected mean,
`𝔼(Y) − ½𝕄ad(Y) = inf {∫_{(0,1]} 𝔸𝕍@ℝ_α(Y) dm(α) : m ∈ 𝒫(0, 1], ∫_{(0,1)} (1/v) dm(v) ≤ 1}`. -/
theorem mad_kusuoka {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : IsNonAtomic P) (Y : Ω → ℝ) (hY : MemLp Y 1 P) :
    IsGLB {x : ℝ | ∃ m : Measure ℝ, IsProbabilityMeasure m ∧ m (Set.Ioc 0 1)ᶜ = 0 ∧
        (∫⁻ v in Set.Ioo 0 1, ENNReal.ofReal (1 / v) ∂m) ≤ 1 ∧
        x = ∫ α in Set.Ioc 0 1, averageValueAtRisk P Y α ∂m}
      ((∫ ω, Y ω ∂P) - (1 / 2) * meanAbsoluteDeviation P Y) := by sorry

end RiskFunctionals.Kusuoka
