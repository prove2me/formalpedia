-- Prove2me | Theorems.Thm_QuerySampleRev_Supplement_theorem_18
-- name    : QuerySampleRev.Supplement.theorem_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:22:48.427948+00:00
-- url     : https://prove2.me/theorems/7a10c535-8f5b-475a-9071-831829e9ede6
-- title:
--   Theorem 18 — quasi-MHR: one sample, then $O\big(\varepsilon^{-3}\log\frac1\delta\big)$ pricing queries suffice
-- statement:
--   **Theorem 18.** There is an absolute constant $C>0$ such that for every $0<\varepsilon\le1/4$ and $0<\delta\le1/4$ there is a learning algorithm that is $(\varepsilon,\delta)$-PAC for the family of quasi-MHR distributions and first draws a single value sample (round $0$) and then makes at most
--   $$ \frac{C}{\varepsilon^{3}}\log\frac1\delta $$
--   pricing queries on every execution, drawing no further sample.
--
--   This is the single-sample query complexity upper bound for quasi-MHR distributions; together with the paper's lower bounds it locates the query-sample tradeoff for this family.
--
--   **Formalization Note** $C$ is chosen before $\varepsilon$ and $\delta$. Counts are the numbers of sample and query rounds before the stopping round; bounded counts force every run to stop. The family is the mission's published quasi-MHR family.
--
--   Differences from the source:
--   - reading: $O(\cdot)$ → one absolute constant $C>0$ chosen before $\varepsilon,\delta$; reason: the standard reading of an asymptotic bound with explicit parameters; the stronger (uniform) reading
--   - encoding: first draws a single (value) sample and then makes at most $N$ pricing queries → on every execution: round $0$ is a sample round, it is the only sample round before stopping, and the number of query rounds before stopping is $\le N$; reason: §2.2: an upper bound on either count holds on every execution
--   - encoding: randomized adaptive learner of §2.2 → a measurable action rule of a uniform seed and the past observations, run on an i.i.d. value stream; reason: one uniform seed generates any internal randomization; same learners
--   - encoding: query and output prices $p\ge0$ → the learner may use any real price; reason: values are $\ge0$ almost surely, so a query at $p\le0$ is answered $1$ and an output $p\le0$ earns $0$; a learner using such prices is matched by one using $p=0$, so the existence claim is unchanged
--   - encoding: quasi-MHR distributions (on $[0,\infty)$, with finite optimal revenue) → probability measures on $\mathbb R$ with no mass on $(-\infty,0)$, quasi-MHR, $r^*<\infty$; reason: the standing assumptions of §2.1–2.2
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), Theorem 18, p.32 (PDF p.34)

import Mathlib
import Definitions.Def_QuerySampleRev_IsPAC

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev.Supplement

open QuerySampleRev

/-- **Theorem 18 (Upper Bound for Quasi-MHR Distributions).** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue Maximization* (manuscript, sha256 c31ea3d3…), Theorem 18, p.32 (PDF 34): "Fix `0 < ε, δ ≤ 1/4`. For the family of quasi-MHR distributions, there exists an `(ε, δ)`-PAC learning algorithm that first draws one value sample and then makes at most `O((1/ε³) log(1/δ))` pricing queries."

The `O(·)` is one absolute constant `C > 0`, chosen before `ε` and `δ`. The access pattern holds on every
execution (every seed and value stream, §2.2: "Unless stated otherwise, an upper bound on either count holds
on every execution"). "First draws a single sample and then makes pricing queries": round `0` is a sample round and it is the
only sample round before stopping (`sampleCount = 1`), and the number of query rounds before stopping is at
most the bound. Bounded counts force every run to stop.

The family is the published quasi-MHR family (`IsPAC`). -/
theorem theorem_18 :
    ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
        ∃ L : Learner, IsPAC L ε δ ∧
          (∀ ω : Outcome, actAt L ω 0 = Act.sample ∧ sampleCount L ω = 1 ∧
            (queryCount L ω : ℝ≥0∞) ≤ ENNReal.ofReal (C / ε ^ 3 * Real.log (1 / δ))) := by sorry

end QuerySampleRev.Supplement
