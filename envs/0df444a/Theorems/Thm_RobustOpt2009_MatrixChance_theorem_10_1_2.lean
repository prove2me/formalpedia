-- Prove2me | Theorems.Thm_RobustOpt2009_MatrixChance_theorem_10_1_2
-- name    : RobustOpt2009.MatrixChance.theorem_10_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:43:46.3548+00:00
-- url     : https://prove2.me/theorems/4428ed9f-e092-452c-8fb2-cbef3c9adf7b
-- title:
--   Theorem 10.1.2 — Gaussian matrix perturbation concentration
-- statement:
--   Let $B_1,\ldots,B_L$ be symmetric real $m\times m$ matrices with $\sum_\ell B_\ell^2\preceq I$. Let $\zeta_1,\ldots,\zeta_L$ be independent measurable $N(0,1)$ variables. For $\Upsilon>0$, set $\chi=\Pr\{\|\sum_\ell\zeta_\ell B_\ell\|\le\Upsilon\}>1/2$. Then for every $\Omega\ge\Upsilon$,
--   $$\Pr\left\{\left\|\sum_\ell\zeta_\ell B_\ell\right\|>\Omega\right\}\le T\left(q(1-\chi)+(\Omega-\Upsilon)\max\{1,\Upsilon^{-1}q(1-\chi)\}\right)\le\exp\left(-\frac{\Omega^2\Upsilon^{-2}q(1-\chi)^2}{2}\right).$$
--   The norm is the Euclidean operator norm. This Gaussian concentration milestone retains the second exponential bound and the non-strict threshold $\Omega\ge\Upsilon$.
--
--   **Formalization Note** Matrices and perturbation coordinates have positive finite dimensions, indexed from zero in Lean. Probabilities are real values of probability measures. The function $T(t)=\Pr\{G>t\}$ for $G\sim N(0,1)$ is the book's upper-tail Erf, not the usual error function. Its quantile $q(p)=\inf\{t\in\overline{\mathbb R}:T(t)\le p\}$ is extended by $q(0)=+\infty$ and $q(1)=-\infty$; $T(+\infty)=0$ and $e^{-\infty^2/2}=0$. This makes the probability-one endpoint, not specified by (2.3.22), explicit without removing it. Finite arguments give exactly the displayed source formulas.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Theorem 10.1.2, printed p. 240 (PDF p. 266).

import Definitions.Def_RobustOpt2009_MatrixChance_Setting

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RobustOpt2009.MatrixChance

theorem theorem_10_1_2 {W : Type*} [MeasurableSpace W]
    (μ : Measure W) [IsProbabilityMeasure μ] {m L : ℕ} [NeZero m] [NeZero L]
    (B : Fin L → Matrix (Fin m) (Fin m) ℝ)
    (hB : ∀ l, (B l).IsSymm) (hvariance : (1 - ∑ l, B l * B l).PosSemidef)
    (ζ : Fin L → W → ℝ) (hmeas : ∀ l, Measurable (ζ l))
    (hindep : iIndepFun ζ μ) (hgaussian : gaussianCase μ ζ)
    (Υ χ : ℝ) (hΥ : 0 < Υ)
    (hχeq : χ = (μ {w | spectralNorm (perturbation B (fun l => ζ l w)) ≤ Υ}).toReal)
    (hχ : (1 / 2 : ℝ) < χ) :
    ∀ Ω : ℝ, Υ ≤ Ω →
      (μ {w | Ω < spectralNorm (perturbation B (fun l => ζ l w))}).toReal ≤
        normalTail (amplificationArgument χ Υ Ω) ∧
      normalTail (amplificationArgument χ Υ Ω) ≤
        gaussianEnvelope (((Ω / Υ : ℝ) : EReal) * tailQuantile (1 - χ)) := by sorry

end RobustOpt2009.MatrixChance
