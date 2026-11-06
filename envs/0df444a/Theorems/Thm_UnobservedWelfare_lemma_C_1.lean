-- Prove2me | Theorems.Thm_UnobservedWelfare_lemma_C_1
-- name    : UnobservedWelfare.lemma_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:28:53.593694+00:00
-- url     : https://prove2.me/theorems/c2f080cd-3865-4886-8d2f-17643f4df003
-- title:
--   Lemma C.1 — centered exponential moment under a log-concave survival function
-- statement:
--   Let $U$ be a real random variable with $\mathbb E|U|<\infty$, $\mathbb E[U]=0$, a continuous distribution and a log-concave survival function $s\mapsto\Pr(U>s)$. Write $U_-=(-U)_+$. For every $\kappa>e\,\mathbb E[U_-]$, $e^{U/\kappa}$ is integrable and
--   $$\mathbb E[e^{U/\kappa}]-1\le\frac1{\kappa^2}\Big(\frac12+\frac{e}{1-e\,\mathbb E[U_-]/\kappa}\Big)\mathbb E[U_-^2],$$
--   in the extended sense if $\mathbb E[U_-^2]=\infty$.
--
--   This controls the centered fluctuations in the scalar sale estimate (Lemma 4.3).
--
--   **Formalization Note** Log-concavity of the survival function is the platform predicate `ConvexOptimization.LogConcaveOn` on $\mathbb R$, which allows the value $0$.
--
--   Differences from the source:
--   - encoding: "a nonconstant real random variable ... having a continuous distribution" → a measurable $U$ with $\Pr(U=s)=0$ for every $s$; no separate nonconstancy hypothesis; reason: on a probability space a continuous distribution is never a point mass
--   - encoding: the bound "understood in the extended sense if $\mathbb E[U_-^2]=\infty$" → `ENNReal.ofReal (E[e^{U/κ}] − 1) ≤ ENNReal.ofReal(coefficient) * ∫⁻ (U₋)²`; reason: equal to the real inequality when $\mathbb E[U_-^2]<\infty$ (the right side is nonnegative), and the extended reading otherwise
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), Lemma C.1, p.46 (PDF p.48)

import Mathlib
import Definitions.Def_LogConcaveOn

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace UnobservedWelfare

/-- **Lemma C.1 (centered exponential moment)** (Cheng–Tao–Xing, *Maximizing Unobserved Welfare: Logarithmic Regret from Purchases*, manuscript (STOC 2027 submission), Lemma C.1, p.46 (PDF p.48)). Let `U` be a
nonconstant real random variable with `E[U] = 0` and `E[|U|] < ∞`, having a continuous
distribution and a log-concave survival function, and write `U₋ := (−U)₊`. For every
`κ > e E[U₋]`, `E[e^{U/κ}] − 1 ≤ κ^{−2} (1/2 + e/(1 − e E[U₋]/κ)) E[U₋²]`; the exponential
expectation is finite, and the bound is understood in the extended sense if `E[U₋²] = ∞`.

**Formalization Note** "Continuous distribution" is `P(U = s) = 0` for every `s`, which already
makes `U` nonconstant on a probability space. "Log-concave survival function" is the platform
predicate `ConvexOptimization.LogConcaveOn` (log-concavity with the value `0` allowed) of
`s ↦ P(U > s)` on `ℝ`. The extended-sense bound is stated in `[0, ∞]`: the left side is truncated at
`0` and `E[U₋²]` is a lower Lebesgue integral. -/
theorem lemma_C_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → ℝ) (hUm : Measurable U) (hUi : Integrable U μ) (hU0 : ∫ ω, U ω ∂μ = 0)
    (hcont : ∀ s : ℝ, μ {ω | U ω = s} = 0)
    (hlc : ConvexOptimization.LogConcaveOn Set.univ (fun s : ℝ => (μ {ω | s < U ω}).toReal))
    (κ : ℝ) (hκ : Real.exp 1 * ∫ ω, max (-U ω) 0 ∂μ < κ) :
    Integrable (fun ω => Real.exp (U ω / κ)) μ ∧
    ENNReal.ofReal (∫ ω, Real.exp (U ω / κ) ∂μ - 1) ≤
      ENNReal.ofReal (1 / κ ^ 2 *
        (1 / 2 + Real.exp 1 / (1 - Real.exp 1 * (∫ ω, max (-U ω) 0 ∂μ) / κ))) *
      ∫⁻ ω, ENNReal.ofReal (max (-U ω) 0 ^ 2) ∂μ := by sorry

end UnobservedWelfare
