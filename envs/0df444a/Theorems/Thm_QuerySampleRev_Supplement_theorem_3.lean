-- Prove2me | Theorems.Thm_QuerySampleRev_Supplement_theorem_3
-- name    : QuerySampleRev.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:18:38.4434+00:00
-- url     : https://prove2.me/theorems/3f4c6b27-44a3-40a5-9868-b588751a9dab
-- title:
--   Theorem 3 — quasi-regular: one sample, then $O\big(\varepsilon^{-3}\log\frac1\varepsilon\log\frac1\delta\big)$ pricing queries suffice
-- statement:
--   **Theorem 3.** There is an absolute constant $C>0$ such that for every $0<\varepsilon\le1/4$ and $0<\delta\le1/4$ there is a learning algorithm that is $(\varepsilon,\delta)$-PAC for the family of quasi-regular distributions and first draws a single value sample (round $0$) and then makes at most
--   $$ \frac{C}{\varepsilon^{3}}\log\frac1\varepsilon\log\frac1\delta $$
--   pricing queries on every execution, drawing no further sample.
--
--   This is the single-sample query complexity upper bound for quasi-regular distributions; together with the paper's lower bounds it locates the query-sample tradeoff for this family.
--
--   **Formalization Note** $C$ is chosen before $\varepsilon$ and $\delta$. Counts are the numbers of sample and query rounds before the stopping round; bounded counts force every run to stop.
--
--   Differences from the source:
--   - reading: $O(\cdot)$ → one absolute constant $C>0$ chosen before $\varepsilon,\delta$; reason: the standard reading of an asymptotic bound with explicit parameters; the stronger (uniform) reading
--   - reading: no range printed for $\varepsilon,\delta$ → $0<\varepsilon,\delta\le1/4$; reason: the range the proof fixes ('Throughout the proof, we assume ε, δ ≤ 1/4') and the range printed in the parallel single-sample Theorems 15, 18 and 26; an $O(\cdot)$ bound printed without a range is read on the range on which the paper proves it
--   - encoding: first draws a single (value) sample and then makes at most $N$ pricing queries → on every execution: round $0$ is a sample round, it is the only sample round before stopping, and the number of query rounds before stopping is $\le N$; reason: §2.2: an upper bound on either count holds on every execution
--   - encoding: randomized adaptive learner of §2.2 → a measurable action rule of a uniform seed and the past observations, run on an i.i.d. value stream; reason: one uniform seed generates any internal randomization; same learners
--   - encoding: query and output prices $p\ge0$ → the learner may use any real price; reason: values are $\ge0$ almost surely, so a query at $p\le0$ is answered $1$ and an output $p\le0$ earns $0$; a learner using such prices is matched by one using $p=0$, so the existence claim is unchanged
--   - encoding: quasi-regular distributions (on $[0,\infty)$, with finite optimal revenue) → probability measures on $\mathbb R$ with no mass on $(-\infty,0)$, quasi-regular, $r^*<\infty$; reason: the standing assumptions of §2.1–2.2
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), Theorem 3, p.16 (PDF p.18); proof, p.16: 'Throughout the proof, we assume ε, δ ≤ 1/4'

import Mathlib
import Definitions.Def_QuerySampleRev_Supplement_IsPACFor
import Definitions.Def_QuerySampleRev_Supplement_IsQuasiRegular

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev.Supplement

open QuerySampleRev

/-- **Theorem 3 (Upper Bound for Quasi-Regular Distributions).** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue Maximization* (manuscript, sha256 c31ea3d3…), Theorem 3, p.16 (PDF 18): "For the family of quasi-regular distributions, there exists an `(ε, δ)`-PAC learning algorithm that first draws a single sample and then makes at most `O((1/ε³) log(1/ε) log(1/δ))` pricing queries." Proof, p.16: "Throughout the proof, we assume `ε, δ ≤ 1/4`"

The `O(·)` is one absolute constant `C > 0`, chosen before `ε` and `δ`. The access pattern holds on every
execution (every seed and value stream, §2.2: "Unless stated otherwise, an upper bound on either count holds
on every execution"). "First draws a single sample and then makes pricing queries": round `0` is a sample round and it is the
only sample round before stopping (`sampleCount = 1`), and the number of query rounds before stopping is at
most the bound. Bounded counts force every run to stop.

**Formalization Note.** The range `0 < ε, δ ≤ 1/4` is the one the proof fixes ("Throughout the proof, we assume `ε, δ ≤ 1/4`"). -/
theorem theorem_3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
        ∃ L : Learner, IsPACFor IsQuasiRegular L ε δ ∧
          (∀ ω : Outcome, actAt L ω 0 = Act.sample ∧ sampleCount L ω = 1 ∧
            (queryCount L ω : ℝ≥0∞) ≤ ENNReal.ofReal (C / ε ^ 3 * Real.log (1 / ε) * Real.log (1 / δ))) := by sorry

end QuerySampleRev.Supplement
