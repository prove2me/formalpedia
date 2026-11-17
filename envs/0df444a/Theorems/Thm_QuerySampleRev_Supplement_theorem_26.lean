-- Prove2me | Theorems.Thm_QuerySampleRev_Supplement_theorem_26
-- name    : QuerySampleRev.Supplement.theorem_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:25:11.345432+00:00
-- url     : https://prove2.me/theorems/40157e9b-f505-4d2f-b7ab-85fe050547c5
-- title:
--   Theorem 26 — MHR: one sample, then $O\big(\varepsilon^{-2}\log\frac1\delta\big)$ pricing queries suffice
-- statement:
--   **Theorem 26.** There is an absolute constant $C>0$ such that for every $0<\varepsilon\le1/4$ and $0<\delta\le1/4$ there is a learning algorithm that is $(\varepsilon,\delta)$-PAC for the family of MHR distributions and first draws a single value sample (round $0$) and then makes at most
--   $$ \frac{C}{\varepsilon^{2}}\log\frac1\delta $$
--   pricing queries on every execution, drawing no further sample.
--
--   This is the single-sample query complexity upper bound for MHR distributions; together with the paper's lower bounds it locates the query-sample tradeoff for this family.
--
--   **Formalization Note** $C$ is chosen before $\varepsilon$ and $\delta$. Counts are the numbers of sample and query rounds before the stopping round; bounded counts force every run to stop.
--
--   Differences from the source:
--   - reading: $O(\cdot)$ → one absolute constant $C>0$ chosen before $\varepsilon,\delta$; reason: the standard reading of an asymptotic bound with explicit parameters; the stronger (uniform) reading
--   - encoding: first draws a single (value) sample and then makes at most $N$ pricing queries → on every execution: round $0$ is a sample round, it is the only sample round before stopping, and the number of query rounds before stopping is $\le N$; reason: §2.2: an upper bound on either count holds on every execution
--   - encoding: randomized adaptive learner of §2.2 → a measurable action rule of a uniform seed and the past observations, run on an i.i.d. value stream; reason: one uniform seed generates any internal randomization; same learners
--   - encoding: query and output prices $p\ge0$ → the learner may use any real price; reason: values are $\ge0$ almost surely, so a query at $p\le0$ is answered $1$ and an output $p\le0$ earns $0$; a learner using such prices is matched by one using $p=0$, so the existence claim is unchanged
--   - encoding: MHR distributions (on $[0,\infty)$, with finite optimal revenue) → probability measures on $\mathbb R$ with no mass on $(-\infty,0)$, MHR, $r^*<\infty$; reason: the standing assumptions of §2.1–2.2
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), Theorem 26, p.40 (PDF p.42)

import Mathlib
import Definitions.Def_QuerySampleRev_Supplement_IsPACFor
import Definitions.Def_QuerySampleRev_Supplement_IsMHR

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev.Supplement

open QuerySampleRev

/-- **Theorem 26 (Upper Bound for MHR Distributions).** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue Maximization* (manuscript, sha256 c31ea3d3…), Theorem 26, p.40 (PDF 42): "Fix `0 < ε, δ ≤ 1/4`. For the family of MHR distributions, there exists an `(ε, δ)`-PAC learning algorithm that first draws one value sample and then makes at most `O((1/ε²) log(1/δ))` pricing queries."

The `O(·)` is one absolute constant `C > 0`, chosen before `ε` and `δ`. The access pattern holds on every
execution (every seed and value stream, §2.2: "Unless stated otherwise, an upper bound on either count holds
on every execution"). "First draws a single sample and then makes pricing queries": round `0` is a sample round and it is the
only sample round before stopping (`sampleCount = 1`), and the number of query rounds before stopping is at
most the bound. Bounded counts force every run to stop. -/
theorem theorem_26 :
    ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
        ∃ L : Learner, IsPACFor IsMHR L ε δ ∧
          (∀ ω : Outcome, actAt L ω 0 = Act.sample ∧ sampleCount L ω = 1 ∧
            (queryCount L ω : ℝ≥0∞) ≤ ENNReal.ofReal (C / ε ^ 2 * Real.log (1 / δ))) := by sorry

end QuerySampleRev.Supplement
