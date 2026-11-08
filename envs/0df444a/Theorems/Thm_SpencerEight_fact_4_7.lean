-- Prove2me | Theorems.Thm_SpencerEight_fact_4_7
-- name    : SpencerEight.fact_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:12:35.048623+00:00
-- url     : https://prove2.me/theorems/a43f194a-8b01-47e3-b64d-865399251545
-- title:
--   Fact 4.7 — matrix Hoeffding bound for biased signs
-- statement:
--   Let $A_1,\dots,A_m\in\mathbb R^{N\times N}$ be symmetric with $\sum_iA_i^2\preceq\sigma^2I_N$ for some $\sigma>0$, and let $\varepsilon_1,\dots,\varepsilon_m\in\{-1,1\}$ be independent with $\mathbb E[\varepsilon_i]=y_i$. Then, for every $t\ge0$,
--   $$\Pr\Bigl[\bigl\|\sum_{i=1}^m(\varepsilon_i-y_i)A_i\bigr\|\ge t\Bigr]\le2N\exp\Bigl(-\frac{t^2}{2\sigma^2}\Bigr).$$
--   In particular, $\|\sum_i(\varepsilon_i-y_i)A_i\|\le\sqrt{2\sigma^2\log(4N)}$ with probability at least $1/2$.
--
--   With uniform signs this settles the small dimensions of the goal theorem.
--
--   Differences from the source:
--   - encoding: A_i ∈ ℝ^{N×N} → 1 ≤ N; reason: a nondegeneracy condition: the tail bound fails at N = 0, t = 0, and log(4N) needs N ≥ 1
--   - encoding: independent signs with mean y_i → measurable ε_i on a probability space, iIndepFun, values ±1 at every ω, ∫ε_i = y_i; reason: the standard formalization of the hypothesis
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Fact 4.7, p.27 (PDF p.27)

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
open scoped ENNReal

namespace SpencerEight

/-- Fact 4.7 (Matrix Hoeffding bound for biased signs), Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.27 (PDF p.27). The tail bound for every `t ≥ 0`, and the bound with probability at least `1/2`.

**Formalization Note** `N ≥ 1`: at `N = 0`, `t = 0` the tail bound fails, and the lemma's `log(4N)` needs it. The `ε_i` are independent `{−1, 1}`-valued random variables on a probability space with mean `y_i`. -/
theorem fact_4_7 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m N : ℕ} (hN : 1 ≤ N) (A : Fin m → Matrix (Fin N) (Fin N) ℝ) (hA : ∀ i, (A i).IsSymm)
    {σ : ℝ} (hσ : 0 < σ)
    (hS : (σ ^ 2 • (1 : Matrix (Fin N) (Fin N) ℝ) - ∑ i, A i ^ 2).PosSemidef)
    (ε : Fin m → Ω → ℝ) (hεm : ∀ i, Measurable (ε i)) (hεi : iIndepFun ε P)
    (hε : ∀ i ω, ε i ω = 1 ∨ ε i ω = -1) (y : Fin m → ℝ) (hy : ∀ i, ∫ ω, ε i ω ∂P = y i) :
    (∀ t : ℝ, 0 ≤ t →
      P {ω | t ≤ ‖∑ i, (ε i ω - y i) • A i‖} ≤
        ENNReal.ofReal (2 * N * Real.exp (-t ^ 2 / (2 * σ ^ 2)))) ∧
    (1 / 2 : ℝ≥0∞) ≤
      P {ω | ‖∑ i, (ε i ω - y i) • A i‖ ≤ Real.sqrt (2 * σ ^ 2 * Real.log (4 * N))} := by sorry

end SpencerEight
