-- Prove2me | Theorems.Thm_QuerySampleRev_Supplement_theorem_36
-- name    : QuerySampleRev.Supplement.theorem_36
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:19:16.586802+00:00
-- url     : https://prove2.me/theorems/b0a343fd-571f-4b6a-855e-85397f17f62a
-- title:
--   Theorem 36 — quasi-regular: $O\big(\varepsilon^{-3}\log\frac1\delta\big)$ samples and no pricing queries suffice
-- statement:
--   **Theorem 36.** There is an absolute constant $C>0$ such that for every $0<\varepsilon\le1/4$ and $0<\delta\le1/4$ there is a learning algorithm that is $(\varepsilon,\delta)$-PAC for the family of quasi-regular distributions and draws at most
--   $$ \frac{C}{\varepsilon^{3}}\log\frac1\delta $$
--   value samples and makes no pricing query, on every execution.
--
--   This is the sample complexity upper bound (sample access only) for quasi-regular distributions; together with the paper's lower bounds it locates the query-sample tradeoff for this family.
--
--   **Formalization Note** $C$ is chosen before $\varepsilon$ and $\delta$. Counts are the numbers of sample and query rounds before the stopping round; bounded counts force every run to stop.
--
--   Differences from the source:
--   - reading: $O(\cdot)$ → one absolute constant $C>0$ chosen before $\varepsilon,\delta$; reason: the standard reading of an asymptotic bound with explicit parameters; the stronger (uniform) reading
--   - encoding: draws at most $N$ samples and makes no pricing queries → on every execution: at most $N$ sample rounds and no query round before stopping; reason: §2.2: an upper bound on either count holds on every execution
--   - encoding: randomized adaptive learner of §2.2 → a measurable action rule of a uniform seed and the past observations, run on an i.i.d. value stream; reason: one uniform seed generates any internal randomization; same learners
--   - encoding: query and output prices $p\ge0$ → the learner may use any real price; reason: values are $\ge0$ almost surely, so a query at $p\le0$ is answered $1$ and an output $p\le0$ earns $0$; a learner using such prices is matched by one using $p=0$, so the existence claim is unchanged
--   - encoding: quasi-regular distributions (on $[0,\infty)$, with finite optimal revenue) → probability measures on $\mathbb R$ with no mass on $(-\infty,0)$, quasi-regular, $r^*<\infty$; reason: the standing assumptions of §2.1–2.2
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), Theorem 36 (Restated), p.22 (PDF p.24); Theorem 36, Appendix B.1, p.47 (PDF p.49)

import Mathlib
import Definitions.Def_QuerySampleRev_Supplement_IsPACFor
import Definitions.Def_QuerySampleRev_Supplement_IsQuasiRegular

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev.Supplement

open QuerySampleRev

/-- **Theorem 36 (Restated; Upper Bound for Quasi-Regular Distributions, sample access).** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue Maximization* (manuscript, sha256 c31ea3d3…), Theorem 36 (Restated), p.22 (PDF 24); Appendix B.1, p.47 (PDF 49): "Fix `0 < ε, δ ≤ 1/4`. For the family of quasi-regular distributions, there exists an `(ε, δ)`-PAC learning algorithm that draws at most `O((1/ε³) log(1/δ))` many samples and makes no pricing queries."

The `O(·)` is one absolute constant `C > 0`, chosen before `ε` and `δ`. The access pattern holds on every
execution (every seed and value stream, §2.2: "Unless stated otherwise, an upper bound on either count holds
on every execution"). "Draws at most N samples and makes no pricing queries": the number of sample rounds before stopping is at
most the bound and there is no query round. Bounded counts force every run to stop.

**Formalization Note.** The range `0 < ε, δ ≤ 1/4` is the one printed in the restated theorem. -/
theorem theorem_36 :
    ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
        ∃ L : Learner, IsPACFor IsQuasiRegular L ε δ ∧
          (∀ ω : Outcome,
            (sampleCount L ω : ℝ≥0∞) ≤ ENNReal.ofReal (C / ε ^ 3 * Real.log (1 / δ)) ∧ queryCount L ω = 0) := by sorry

end QuerySampleRev.Supplement
