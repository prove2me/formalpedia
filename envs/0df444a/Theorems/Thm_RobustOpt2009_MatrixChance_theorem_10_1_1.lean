-- Prove2me | Theorems.Thm_RobustOpt2009_MatrixChance_theorem_10_1_1
-- name    : RobustOpt2009.MatrixChance.theorem_10_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:43:42.957127+00:00
-- url     : https://prove2.me/theorems/7884f9ce-8913-4359-ab49-ff7847ca83be
-- title:
--   Theorem 10.1.1 — bounded matrix perturbation concentration
-- statement:
--   Let $B_1,\ldots,B_L$ be symmetric real $m\times m$ matrices with $\sum_\ell B_\ell^2\preceq I$. Let $\zeta_1,\ldots,\zeta_L$ be independent measurable real random variables taking values in $[-1,1]$, with zero means as stipulated at the start of Section 10.1. For $\Upsilon>0$, put $\chi=\Pr\{\|\sum_\ell\zeta_\ell B_\ell\|\le\Upsilon\}>0$. Then, for every $\Omega>\Upsilon$,
--   $$\Pr\left\{\left\|\sum_\ell\zeta_\ell B_\ell\right\|>\Omega\right\}\le\chi^{-1}\exp\left(-\frac{(\Omega-\Upsilon)^2}{16}\right).$$
--   The norm is the Euclidean operator norm. This is the bounded-variable concentration milestone. The initial probability is an equality, as in (10.1.9).
--
--   **Formalization Note** Positive dimensions are represented by nonzero natural numbers. Almost-sure boundedness and measurability ensure integrability of the real coordinates; the expectation is not a default value for a nonintegrable function.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Theorem 10.1.1, printed p. 239 (PDF p. 265); standing assumptions, printed p. 237 (PDF p. 263).

import Definitions.Def_RobustOpt2009_MatrixChance_Setting

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RobustOpt2009.MatrixChance

theorem theorem_10_1_1 {W : Type*} [MeasurableSpace W]
    (μ : Measure W) [IsProbabilityMeasure μ] {m L : ℕ} [NeZero m] [NeZero L]
    (B : Fin L → Matrix (Fin m) (Fin m) ℝ)
    (hB : ∀ l, (B l).IsSymm) (hvariance : (1 - ∑ l, B l * B l).PosSemidef)
    (ζ : Fin L → W → ℝ) (hmeas : ∀ l, Measurable (ζ l))
    (hindep : iIndepFun ζ μ) (hbounded : boundedCase μ ζ)
    (Υ χ : ℝ) (hΥ : 0 < Υ)
    (hχeq : χ = (μ {w | spectralNorm (perturbation B (fun l => ζ l w)) ≤ Υ}).toReal)
    (hχ : 0 < χ) :
    ∀ Ω : ℝ, Υ < Ω →
      (μ {w | Ω < spectralNorm (perturbation B (fun l => ζ l w))}).toReal ≤
        (1 / χ) * Real.exp (-((Ω - Υ) ^ 2) / 16) := by sorry

end RobustOpt2009.MatrixChance
