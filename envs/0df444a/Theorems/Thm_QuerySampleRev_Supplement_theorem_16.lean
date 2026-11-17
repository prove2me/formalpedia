-- Prove2me | Theorems.Thm_QuerySampleRev_Supplement_theorem_16
-- name    : QuerySampleRev.Supplement.theorem_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:22:07.032657+00:00
-- url     : https://prove2.me/theorems/d0a8c456-9a8f-4d7a-8d1f-593ab907dee6
-- title:
--   Theorem 16 — regular lower bound: $\le \frac C{\varepsilon^3}\log\frac1\delta$ samples force $\ge \frac C{\varepsilon^3}\log\frac1\delta$ expected queries
-- statement:
--   **Theorem 16.** There is an absolute constant $C>0$ such that the following holds. Fix $0<\delta\le1/4$ and $0<\varepsilon\le1/48$. If a learning algorithm is $(\varepsilon,\delta)$-PAC for regular distributions and draws at most
--   $$
--   \frac{C}{\varepsilon^{3}}\log\frac1\delta
--   $$
--   value samples on every execution, then there is a regular distribution $F$ on which its expected number of pricing queries is at least
--   $$
--   \mathbb E_F[T]\ \ge\ \frac{C}{\varepsilon^{3}}\log\frac1\delta.
--   $$
--   It shows that the corresponding upper bounds of the paper cannot be improved by more than a constant factor in this sample regime.
--
--   **Formalization Note** $C$ is chosen before $\delta$, $\varepsilon$ and the learner. The sample budget holds for every seed and every value stream; the expectation is the lower integral of the query count in $[0,\infty]$. Learners may be randomized, interleave samples and queries adaptively and stop adaptively.
--
--   Differences from the source:
--   - generalization: learners that terminate (at termination the algorithm outputs a price) → learners that may fail to stop; a run that never stops fails the PAC event; no termination hypothesis; reason: for learners that terminate almost surely the PAC condition is the source's, so the statement specializes to the source
--   - generalization: learners choose query prices $p_t\ge0$ → learners may query and output any real price; reason: a larger class of learners; a query at $p\le0$ is answered $1$ almost surely, so the class contains every learner of §2.2
--   - encoding: randomized adaptive learner of §2.2 → a measurable action rule of a uniform seed and the past observations, run on an i.i.d. value stream; reason: one uniform seed generates any internal randomization; same learners
--   - encoding: expectations of the counts → lower Lebesgue integrals of $\mathbb N\cup\{\infty\}$-valued counts, in $[0,\infty]$; reason: no integrability condition is needed; the value is $+\infty$ when the expectation is infinite
--   - encoding: regular distributions (on $[0,\infty)$, with finite optimal revenue) → probability measures on $\mathbb R$ with no mass on $(-\infty,0)$, regular, $r^*<\infty$; reason: the standing assumptions of §2.1–2.2
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), Theorem 16, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_QuerySampleRev_Supplement_IsPACFor
import Definitions.Def_QuerySampleRev_Supplement_IsRegular

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev.Supplement

open QuerySampleRev

/-- **Theorem 16 (Lower Bound for Regular Distributions).** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue Maximization* (manuscript, sha256 c31ea3d3…), Theorem 16, p.30 (PDF 32): "There exists an absolute constant `C > 0` such that the following holds. Fix `0 < δ ≤ 1/4` and `0 < ε ≤ 1/48`. If an `(ε, δ)`-PAC learning algorithm for regular distributions draws at most `(C/ε³) log(1/δ)` value samples, then there exists a regular distribution on which it makes at least `(C/ε³) log(1/δ)` pricing queries in expectation."

One constant `C > 0` works for every admissible `δ`, `ε` and every learner. The sample budget holds on
every execution (§2.2); the conclusion is an expectation (a lower integral in `ℝ≥0∞`) of the number of
pricing queries before stopping. Learners are randomized, adaptive, interleave samples and queries and stop
adaptively; no termination hypothesis is made (a non-terminating run fails the PAC event). -/
theorem theorem_16 :
    ∃ C : ℝ, 0 < C ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 48 →
        ∀ L : Learner, IsPACFor IsRegular L ε δ →
          (∀ ω : Outcome,
            (sampleCount L ω : ℝ≥0∞) ≤ ENNReal.ofReal (C / ε ^ 3 * Real.log (1 / δ))) →
          ∃ μ : Measure ℝ, InFamilyOf IsRegular μ ∧
            ENNReal.ofReal (C / ε ^ 3 * Real.log (1 / δ)) ≤ ∫⁻ ω, (queryCount L ω : ℝ≥0∞) ∂lawP μ := by sorry

end QuerySampleRev.Supplement
