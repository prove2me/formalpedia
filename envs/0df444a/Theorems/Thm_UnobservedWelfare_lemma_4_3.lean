-- Prove2me | Theorems.Thm_UnobservedWelfare_lemma_4_3
-- name    : UnobservedWelfare.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:31:50.489098+00:00
-- url     : https://prove2.me/theorems/84405acd-7738-4d33-a0f3-0e72c03a99dc
-- title:
--   Lemma 4.3 — scalar sale estimate $\kappa\log\mathbb E[e^{[Y-1-\gamma f(Y)]/\kappa}]+\log b\le0$
-- statement:
--   Let $0<\gamma\le1$, $\kappa\ge80/\gamma$ and $f(x)=\tfrac12(1-x)_+^2$. Suppose $Y>0$ is constant or has a continuous distribution with a log-concave survival function, and $\mathbb E[Y]+b=2$ with $b>0$. Then the exponential expectation below is finite and
--   $$\kappa\log\mathbb E\big[e^{[Y-1-\gamma f(Y)]/\kappa}\big]+\log b\le0.\tag{42}$$
--
--   It controls the two Gibbs updates caused by one purchase in the drift bound.
--
--   Differences from the source:
--   - encoding: "$\mathbb E[Y]+b=2$" → `Integrable Y` and $\int Y\,d\mu+b=2$; reason: the equation presupposes a finite mean
--   - encoding: "log-concave survival function" → `ConvexOptimization.LogConcaveOn Set.univ (s ↦ P(Y > s))`; reason: log-concavity allowing the value $0$, as in the source proof ("$\log R$ is concave")
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), Lemma 4.3 (42), p.24 (PDF p.26)

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_UnobservedWelfare_IsRC
import Definitions.Def_UnobservedWelfare_expectedRegret
import Definitions.Def_UnobservedWelfare_gibbsMean
import Definitions.Def_UnobservedWelfare_alg1

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace UnobservedWelfare

/-- **Lemma 4.3 (scalar sale estimate)** (Cheng–Tao–Xing, *Maximizing Unobserved Welfare: Logarithmic Regret from Purchases*, manuscript (STOC 2027 submission), Lemma 4.3 (42), p.24 (PDF p.26)). Let
`0 < γ ≤ 1` and `κ ≥ 80/γ`. Suppose `Y > 0` is constant or has a continuous distribution with a
log-concave survival function. If `E[Y] + b = 2` and `b > 0`, then
`κ log E[e^{[Y − 1 − γ f(Y)]/κ}] + log b ≤ 0`, where `f(x) = (1 − x)₊²/2`; in particular the
exponential expectation is finite.

**Formalization Note** `Y` is integrable (the hypothesis `E[Y] + b = 2` presupposes a finite
mean). Log-concavity of the survival function `s ↦ P(Y > s)` is the platform predicate
`ConvexOptimization.LogConcaveOn` on `ℝ`. The parameter range `0 < γ ≤ 1`, `κ ≥ 80/γ` is the one
fixed in Section 3.1 and Section 4 (pp.20, 22). -/
theorem lemma_4_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (γ κ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hκ : 80 / γ ≤ κ)
    (Y : Ω → ℝ) (hYm : Measurable Y) (hYpos : ∀ ω, 0 < Y ω) (hYi : Integrable Y μ)
    (hY : (∃ y : ℝ, ∀ ω, Y ω = y) ∨
      ((∀ s : ℝ, μ {ω | Y ω = s} = 0) ∧
        ConvexOptimization.LogConcaveOn Set.univ (fun s : ℝ => (μ {ω | s < Y ω}).toReal)))
    (b : ℝ) (hb : 0 < b) (hYb : ∫ ω, Y ω ∂μ + b = 2) :
    Integrable (fun ω => Real.exp ((Y ω - 1 - γ * recCorr (Y ω)) / κ)) μ ∧
    κ * Real.log (∫ ω, Real.exp ((Y ω - 1 - γ * recCorr (Y ω)) / κ) ∂μ) + Real.log b ≤ 0 := by sorry

end UnobservedWelfare
