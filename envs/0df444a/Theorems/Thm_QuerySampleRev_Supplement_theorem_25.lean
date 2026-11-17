-- Prove2me | Theorems.Thm_QuerySampleRev_Supplement_theorem_25
-- name    : QuerySampleRev.Supplement.theorem_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:24:39.131473+00:00
-- url     : https://prove2.me/theorems/845776b4-b07c-4bb0-a073-1b6b16f5cbe0
-- title:
--   Theorem 25 — a sample-only $(\varepsilon,\delta)$-PAC quasi-MHR learner draws $\ge\frac C{\varepsilon^2}\log\frac1\delta$ samples in expectation
-- statement:
--   **Theorem 25.** There is an absolute constant $C>0$ such that for every $0<\delta\le1/4$ and $0<\varepsilon\le1/128$, every learning algorithm that is $(\varepsilon,\delta)$-PAC for quasi-MHR distributions and makes no pricing query on any execution draws, on some quasi-MHR distribution $F$,
--   $$
--   \mathbb E_F[S]\ \ge\ \frac{C}{\varepsilon^{2}}\log\frac1\delta
--   $$
--   value samples in expectation. This matches the sample upper bound of Theorem 38, so $\Theta(\varepsilon^{-2}\log(1/\delta))$ is the sample complexity of quasi-MHR distributions.
--
--   **Formalization Note** $C$ is chosen before $\delta$, $\varepsilon$ and the learner; the expectation is the lower integral of the sample count in $[0,\infty]$. The paper takes $C$ to be the constant of Theorem 21; see the list below.
--
--   Differences from the source:
--   - generalization: learners that terminate (at termination the algorithm outputs a price) → learners that may fail to stop; a run that never stops fails the PAC event; no termination hypothesis; reason: for learners that terminate almost surely the PAC condition is the source's, so the statement specializes to the source
--   - generalization: learners choose query prices $p_t\ge0$ → learners may query and output any real price; reason: a larger class of learners; a query at $p\le0$ is answered $1$ almost surely, so the class contains every learner of §2.2
--   - encoding: randomized adaptive learner of §2.2 → a measurable action rule of a uniform seed and the past observations, run on an i.i.d. value stream; reason: one uniform seed generates any internal randomization; same learners
--   - encoding: expectations of the counts → lower Lebesgue integrals of $\mathbb N\cup\{\infty\}$-valued counts, in $[0,\infty]$; reason: no integrability condition is needed; the value is $+\infty$ when the expectation is infinite
--   - encoding: quasi-MHR distributions (on $[0,\infty)$, with finite optimal revenue) → probability measures on $\mathbb R$ with no mass on $(-\infty,0)$, quasi-MHR, $r^*<\infty$; reason: the standing assumptions of §2.1–2.2
--   - encoding: 'For the absolute constant $C$ in Theorem 21' → $\exists\,C>0$ for Theorem 25 alone; reason: Theorem 21 (published as `QuerySampleRev.theorem_21`) and Theorem 25 both remain true when $C$ is decreased, so given each with some constant, the smaller one serves both; the two forms are equivalent
--   - encoding: 'using only value samples' → no query round before stopping, on every execution; reason: §2.2: an upper bound on either count holds on every execution
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), Theorem 25, p.39 (PDF p.41)

import Mathlib
import Definitions.Def_QuerySampleRev_IsPAC

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev.Supplement

open QuerySampleRev

/-- **Theorem 25 (sample-only lower bound for quasi-MHR distributions).** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue Maximization* (manuscript, sha256 c31ea3d3…), Theorem 25, p.39
(PDF 41): "Fix `0 < δ ≤ 1/4` and `0 < ε ≤ 1/128`. For the absolute constant `C` in Theorem 21, every
`(ε, δ)`-PAC learning algorithm for quasi-MHR distributions using only value samples draws at least
`(C/ε²) log(1/δ)` samples in expectation on some quasi-MHR distribution."

One constant `C > 0` works for every `δ ∈ (0, 1/4]`, `ε ∈ (0, 1/128]` and every learner that makes no pricing
query on any execution; the conclusion is an expectation (a lower integral in `ℝ≥0∞`) of the number of
sample rounds before stopping.

**Formalization Note.** The paper takes `C` to be the constant of Theorem 21 (published as
`QuerySampleRev.theorem_21`). Both statements stay true when `C` is decreased, so a common constant exists
as soon as each holds with some constant; the statement here is the standalone existence of `C`. -/
theorem theorem_25 :
    ∃ C : ℝ, 0 < C ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 128 →
        ∀ L : Learner, IsPAC L ε δ → (∀ ω : Outcome, queryCount L ω = 0) →
          ∃ μ : Measure ℝ, InFamily μ ∧
            ENNReal.ofReal (C / ε ^ 2 * Real.log (1 / δ)) ≤
              ∫⁻ ω, (sampleCount L ω : ℝ≥0∞) ∂lawP μ := by sorry

end QuerySampleRev.Supplement
