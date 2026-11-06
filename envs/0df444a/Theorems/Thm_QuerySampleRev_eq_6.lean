-- Prove2me | Theorems.Thm_QuerySampleRev_eq_6
-- name    : QuerySampleRev.eq_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:38:16.141193+00:00
-- url     : https://prove2.me/theorems/1ff4c364-d977-4db3-ad5c-df1f81df8655
-- title:
--   Inequality (6) — $AK\varepsilon^2\,\mathbb E_{F^{(0)}}[S]+\frac{A\varepsilon^2}{K}\mathbb E_{F^{(0)}}[T]\ge\frac1{16}\log\frac1\delta$
-- statement:
--   Let $c\in[0,1]$, $0<\delta\le1/4$, $0<\varepsilon\le1/128$, $A=100$ and $K=\max\{2,\lfloor\varepsilon^{-c}/64\rfloor\}$. Every learning algorithm that is $(\varepsilon,\delta)$-PAC for quasi-MHR distributions satisfies
--   $$
--   AK\varepsilon^2\,\mathbb E_{F^{(0)}}[S]+\frac{A\varepsilon^2}{K}\,\mathbb E_{F^{(0)}}[T]\ \ge\ \frac1{16}\log\frac1\delta, \tag{6}
--   $$
--   where $S$ and $T$ are its numbers of value samples and pricing queries and $F^{(0)}$ is the base distribution of the construction. No sample budget is assumed.
--
--   Inequality (6) is the tradeoff curve itself: under a sample budget of order $\varepsilon^{c-2}\log(1/\delta)$ the first term is small, which forces $\mathbb E_{F^{(0)}}[T]\gtrsim\varepsilon^{-(2+c)}\log(1/\delta)$.
--
--   Differences from the source:
--   - generalization: learners that terminate (at termination the algorithm outputs a price) → learners that may fail to stop; a run that never stops fails the PAC event; reason: for learners that terminate almost surely the PAC condition is the source's, so the statement specializes to the source
--   - generalization: learners choose query prices $p_t\ge0$ → learners may query and output any real price; reason: a larger class of learners; a query at $p\le0$ is answered $1$ almost surely, so the class contains every learner of §2.2
--   - encoding: randomized adaptive learner of §2.2 → a measurable action rule of a uniform seed and the past observations, run on an i.i.d. value stream; reason: one uniform seed generates any internal randomization; same learners
--   - encoding: expectations of the counts $S$, $T$ → lower Lebesgue integrals of $\mathbb N\cup\{\infty\}$-valued counts, in $[0,\infty]$; reason: no integrability condition is needed; the value is $+\infty$ when the expectation is infinite
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), proof of Theorem 21, p.38 (PDF p.40), inequality (6)

import Mathlib
import Definitions.Def_QuerySampleRev_IsPAC
import Definitions.Def_QuerySampleRev_hardDist

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev

/-- **Inequality (6).** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue Maximization*
(manuscript, sha256 c31ea3d3…), proof of Theorem 21, p.38 (PDF 40): "As in the proof of Theorem 11,
`∑_{i∈[K]} T⁽ⁱ⁾ ≤ T`. Dividing by `K` gives `AKε² E_{F⁽⁰⁾}[S] + (Aε²/K) E_{F⁽⁰⁾}[T] ≥ (1/16) log(1/δ)`. (6)"

For `c ∈ [0, 1]`, `0 < δ ≤ 1/4`, `0 < ε ≤ 1/128`, `A = 100`, `K = max{2, ⌊ε^{−c}/64⌋}`, and every learner
that is `(ε, δ)`-PAC for the quasi-MHR family; expectations are under the base distribution `F⁽⁰⁾`. No
sample budget is assumed. -/
theorem eq_6 {c δ ε : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 128) (L : Learner) (hL : IsPAC L ε δ) :
    ENNReal.ofReal (1 / 16 * Real.log (1 / δ)) ≤
      ENNReal.ofReal (100 * (numHard ε c : ℝ) * ε ^ 2) *
          ∫⁻ ω, (sampleCount L ω : ℝ≥0∞) ∂lawP baseDist +
        ENNReal.ofReal (100 * ε ^ 2 / (numHard ε c : ℝ)) *
          ∫⁻ ω, (queryCount L ω : ℝ≥0∞) ∂lawP baseDist := by sorry

end QuerySampleRev
