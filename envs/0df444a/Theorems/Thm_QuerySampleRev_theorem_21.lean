-- Prove2me | Theorems.Thm_QuerySampleRev_theorem_21
-- name    : QuerySampleRev.theorem_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:38:20.203673+00:00
-- url     : https://prove2.me/theorems/233534f6-bc5a-4f57-8113-734aea1b20a9
-- title:
--   Theorem 21 — an $(\varepsilon,\delta)$-PAC quasi-MHR learner with $\le\frac C{\varepsilon^{2-c}}\log\frac1\delta$ samples makes $\ge\frac C{\varepsilon^{2+c}}\log\frac1\delta$ queries in expectation
-- statement:
--   **Theorem 21 (Lower bound for quasi-MHR distributions).** There is an absolute constant $C>0$ such that the following holds. Fix $c\in[0,1]$, $0<\delta\le1/4$ and $0<\varepsilon\le1/128$. If a learning algorithm is $(\varepsilon,\delta)$-PAC for quasi-MHR distributions and draws at most
--   $$
--   \frac{C}{\varepsilon^{2-c}}\log\frac1\delta
--   $$
--   value samples on every execution, then there is a quasi-MHR distribution $F$ on which its expected number of pricing queries is at least
--   $$
--   \mathbb E_F[T]\ \ge\ \frac{C}{\varepsilon^{2+c}}\log\frac1\delta .
--   $$
--   The learning algorithm may be randomized, may interleave samples and queries adaptively, and may stop adaptively. Together with the matching upper bound (Theorem 20), this shows that for quasi-MHR values every reduction of the sample budget by a factor $\varepsilon^{c}$ below $\varepsilon^{-2}$ must be paid for by $\varepsilon^{-(2+c)}$ pricing queries, interpolating between the sample-only and the query-heavy regimes.
--
--   **Formalization Note** One constant $C$ is chosen before $c,\delta,\varepsilon$ and the learner. The sample budget holds for every seed and every value stream. The expectation is the lower integral of the query count in $[0,\infty]$.
--
--   Differences from the source:
--   - generalization: learners that terminate (at termination the algorithm outputs a price) → learners that may fail to stop; a run that never stops fails the PAC event; no termination hypothesis; reason: for learners that terminate almost surely the PAC condition is the source's, so the statement specializes to the source
--   - generalization: learners choose query prices $p_t\ge0$ → learners may query and output any real price; reason: a larger class of learners; a query at $p\le0$ is answered $1$ almost surely, so the class contains every learner of §2.2
--   - encoding: randomized adaptive learner of §2.2 → a measurable action rule of a uniform seed and the past observations, run on an i.i.d. value stream; reason: one uniform seed generates any internal randomization; same learners
--   - encoding: expectations of the counts $S$, $T$ → lower Lebesgue integrals of $\mathbb N\cup\{\infty\}$-valued counts, in $[0,\infty]$; reason: no integrability condition is needed; the value is $+\infty$ when the expectation is infinite
--   - encoding: quasi-MHR distributions (on $[0,\infty)$, with finite optimal revenue) → the family `InFamily`: probability measures on $\mathbb R$ with no mass on $(-\infty,0)$, quasi-MHR, $r^*<\infty$; reason: the standing assumptions of §2.1–2.2; finite $r^*$ appears both in the PAC requirement and in the witness
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), Theorem 21, p.36 (PDF p.38)

import Mathlib
import Definitions.Def_QuerySampleRev_IsPAC

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev

/-- **Theorem 21 (Lower Bound for Quasi-MHR Distributions).** Jin, Tang, Wang, Zhang, *Query-Sample
Tradeoffs for Revenue Maximization* (manuscript, sha256 c31ea3d3…), Theorem 21, p.36 (PDF 38): "There
exists an absolute constant `C > 0` such that the following holds. Fix `c ∈ [0, 1]`, `0 < δ ≤ 1/4`, and
`0 < ε ≤ 1/128`. If an `(ε, δ)`-PAC learning algorithm for quasi-MHR distributions draws at most
`(C/ε^{2−c}) log(1/δ)` value samples, then there exists a quasi-MHR distribution on which it makes at least
`(C/ε^{2+c}) log(1/δ)` pricing queries in expectation."

One constant `C > 0` works for every `c ∈ [0, 1]`, `δ ∈ (0, 1/4]`, `ε ∈ (0, 1/128]` and every learner. The
sample budget holds on every execution (every seed and value stream, §2.2). The conclusion is an
expectation (a lower integral in `ℝ≥0∞`) of the number of pricing queries before stopping.

**Formalization Note.** Learners are randomized (one uniform seed), adaptive, interleave samples and
queries, and stop adaptively; no termination hypothesis is made (a non-terminating run fails the PAC
event). Value distributions are probability measures on `ℝ` with no mass on `(−∞, 0)`, quasi-MHR and with
finite optimal revenue (`InFamily`). -/
theorem theorem_21 :
    ∃ C : ℝ, 0 < C ∧
      ∀ c : ℝ, 0 ≤ c → c ≤ 1 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 128 →
        ∀ L : Learner, IsPAC L ε δ →
          (∀ ω : Outcome,
            (sampleCount L ω : ℝ≥0∞) ≤ ENNReal.ofReal (C / ε ^ (2 - c) * Real.log (1 / δ))) →
          ∃ μ : Measure ℝ, InFamily μ ∧
            ENNReal.ofReal (C / ε ^ (2 + c) * Real.log (1 / δ)) ≤
              ∫⁻ ω, (queryCount L ω : ℝ≥0∞) ∂lawP μ := by sorry

end QuerySampleRev
