-- Prove2me | Theorems.Thm_WassersteinLinOpt_Ball_tendsto_iff_limsup_quasiIntegral_le
-- name    : WassersteinLinOpt.Ball.tendsto_iff_limsup_quasiIntegral_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T19:15:20.884084+00:00
-- url     : https://prove2.me/theorems/eb175d1c-b194-44dc-bd8a-62af119b0240
-- title:
--   Lemma 3 — Portmanteau characterization by upper semicontinuous functions
-- statement:
--   Throughout, $(X,d)$ is a proper metric space (every closed ball is compact; such a space is complete and separable, hence Polish) with its Borel $\sigma$-algebra, and $p \ge 1$, $r > 0$ are real.
--
--   **Lemma 3.** A sequence $(\mu^k)_k$ in $\mathcal P(X)$ converges weakly to $\mu^\infty\in\mathcal P(X)$ if and only if for every function $g:X\to\mathbb R$ that is bounded above and upper semicontinuous,
--
--   $$\limsup_{k\to\infty}\int_X g\,d\mu^k\le\int_X g\,d\mu^\infty .$$
--
--   This excerpt of the Portmanteau theorem is what Theorem 3's proof uses for a truncated objective.
--
--   **Formalization Note.** Weak convergence is `Filter.Tendsto μs atTop (nhds μlim)` in `ProbabilityMeasure X`. Since $g$ is bounded above, $\int[g]_+$ is finite and the integral is a well-defined value in $[-\infty,\infty)$, taken as `quasiIntegral` in `EReal`; the $\limsup$ is `Filter.limsup` in `EReal`.
-- source:
--   Yue, Kuhn & Wiesemann, On linear optimization over Wasserstein balls, Math. Program. 195 (2022) 1107–1122, https://doi.org/10.1007/s10107-021-01673-8, p. 1120, Lemma 3 (Appendix A)

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_quasiIntegral

open MeasureTheory
open scoped ENNReal NNReal

namespace WassersteinLinOpt.Ball

/-- Lemma 3 (Appendix A, p. 1120; excerpted from the Portmanteau theorem). A sequence `μᵏ` in
`𝒫(X)` converges weakly to `μ^∞` iff `limsup_k ∫ g dμᵏ ≤ ∫ g dμ^∞` for every upper-bounded,
upper semicontinuous `g : X → ℝ`. The integrals are extended-real (they may be `−∞`). -/
theorem tendsto_iff_limsup_quasiIntegral_le {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] (μs : ℕ → ProbabilityMeasure X)
    (μlim : ProbabilityMeasure X) :
    Filter.Tendsto μs Filter.atTop (nhds μlim) ↔
      ∀ g : X → ℝ, BddAbove (Set.range g) → UpperSemicontinuous g →
        Filter.limsup (fun k => quasiIntegral g (μs k : Measure X)) Filter.atTop ≤
          quasiIntegral g (μlim : Measure X) := by sorry

end WassersteinLinOpt.Ball
