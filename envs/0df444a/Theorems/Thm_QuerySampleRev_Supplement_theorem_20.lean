-- Prove2me | Theorems.Thm_QuerySampleRev_Supplement_theorem_20
-- name    : QuerySampleRev.Supplement.theorem_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:23:58.873283+00:00
-- url     : https://prove2.me/theorems/a58c052f-f6e9-4110-a6db-041230d18560
-- title:
--   Theorem 20 — quasi-MHR tradeoff upper bound: $\Theta\big(\varepsilon^{-(2-c)}\log\frac1\delta\big)$ samples first, then $O\big(\varepsilon^{-(2+c)}\log\frac1\delta\big)$ queries
-- statement:
--   **Theorem 20.** There are absolute constants $0<C_1\le C_2$ such that for every $0<\varepsilon\le1/4$, $0<\delta\le1/4$ and $c\in[0,1]$ there is a learning algorithm that is $(\varepsilon,\delta)$-PAC for quasi-MHR distributions and, on every execution,
--
--   1. draws all its value samples before its first pricing query;
--   2. draws a number $S$ of value samples with
--   $$
--   \frac{C_1}{\varepsilon^{2-c}}\log\frac1\delta\ \le\ S\ \le\ \frac{C_2}{\varepsilon^{2-c}}\log\frac1\delta ;
--   $$
--   3. makes at most $\dfrac{C_2}{\varepsilon^{2+c}}\log\dfrac1\delta$ pricing queries.
--
--   This is the upper half of the quasi-MHR tradeoff; the published Theorem 21 is the matching lower bound.
--
--   **Formalization Note** $C_1$ and $C_2$ are chosen before $\varepsilon$, $\delta$ and $c$. "Samples first" says that every sample round before stopping precedes every query round before stopping. $\varepsilon^{2\pm c}$ are real powers. Bounded counts force every run to stop. The family is the mission's published quasi-MHR family.
--
--   Differences from the source:
--   - reading: $\Theta(\cdot)$, $O(\cdot)$ for 'a constant $c\in[0,1]$' → two absolute constants $0<C_1\le C_2$ chosen before $\varepsilon,\delta$ and $c$; reason: the proof draws ⌈Cε^{−(2−c)} log(1/δ)⌉ + 1 samples 'where C is a sufficiently large absolute constant'; the uniform reading is the stronger one
--   - encoding: first draws $\Theta(\cdot)$ value samples and then makes at most $O(\cdot)$ pricing queries → on every execution: every sample round before stopping precedes every query round before stopping, with the count bounds; reason: §2.2: an upper bound on either count holds on every execution; the proof draws all samples before any query
--   - encoding: randomized adaptive learner of §2.2 → a measurable action rule of a uniform seed and the past observations, run on an i.i.d. value stream; reason: one uniform seed generates any internal randomization; same learners
--   - encoding: query and output prices $p\ge0$ → the learner may use any real price; reason: values are $\ge0$ almost surely, so a query at $p\le0$ is answered $1$ and an output $p\le0$ earns $0$; a learner using such prices is matched by one using $p=0$, so the existence claim is unchanged
--   - encoding: quasi-MHR distributions (on $[0,\infty)$, with finite optimal revenue) → probability measures on $\mathbb R$ with no mass on $(-\infty,0)$, quasi-MHR, $r^*<\infty$; reason: the standing assumptions of §2.1–2.2
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), Theorem 20 and its proof, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_QuerySampleRev_IsPAC

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev.Supplement

open QuerySampleRev

/-- **Theorem 20 (Upper Bound for Quasi-MHR Distributions, query-sample tradeoff).** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue Maximization* (manuscript, sha256 c31ea3d3…), Theorem 20,
p.34 (PDF 36): "Fix `0 < ε, δ ≤ 1/4` and a constant `c ∈ [0, 1]`. For the family of quasi-MHR distributions,
there exists an `(ε, δ)`-PAC learning algorithm that first draws `Θ((1/ε^{2−c}) log(1/δ))` value samples and
then makes at most `O((1/ε^{2+c}) log(1/δ))` pricing queries." Proof, p.34: "`m = ⌈Cε^{−(2−c)} log(1/δ)⌉`
samples …, where `C` is a sufficiently large absolute constant. All these samples are drawn before any
pricing query."

The `Θ(·)` and `O(·)` are two absolute constants `0 < C₁ ≤ C₂`, chosen before `ε`, `δ` and `c`. On every
execution: every sample round before stopping precedes every query round before stopping, the number of
sample rounds is between `C₁ x` and `C₂ x` with `x = ε^{−(2−c)} log(1/δ)`, and the number of query rounds is
at most `C₂ ε^{−(2+c)} log(1/δ)`. The family is the published quasi-MHR family (`IsPAC`).

**Formalization Note.** `ε^{2−c}`, `ε^{2+c}` are real powers. Bounded counts force every run to stop. -/
theorem theorem_20 :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ C₁ ≤ C₂ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → ∀ c : ℝ, 0 ≤ c → c ≤ 1 →
        ∃ L : Learner, IsPAC L ε δ ∧
          ∀ ω : Outcome,
            (∀ s t : ℕ, (s : ℕ∞) < stopTime L ω → (t : ℕ∞) < stopTime L ω →
              actAt L ω s = Act.sample → (∃ p, actAt L ω t = Act.query p) → s < t) ∧
            ENNReal.ofReal (C₁ / ε ^ (2 - c) * Real.log (1 / δ)) ≤ (sampleCount L ω : ℝ≥0∞) ∧
            (sampleCount L ω : ℝ≥0∞) ≤ ENNReal.ofReal (C₂ / ε ^ (2 - c) * Real.log (1 / δ)) ∧
            (queryCount L ω : ℝ≥0∞) ≤ ENNReal.ofReal (C₂ / ε ^ (2 + c) * Real.log (1 / δ)) := by sorry

end QuerySampleRev.Supplement
