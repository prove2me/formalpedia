-- Prove2me | Theorems.Thm_QuerySampleRev_Supplement_theorem_11
-- name    : QuerySampleRev.Supplement.theorem_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:20:04.473961+00:00
-- url     : https://prove2.me/theorems/85aa39c2-340f-4162-985f-8c74555d1ea2
-- title:
--   Theorem 11 — quasi-regular lower bound: $\le\frac C{\varepsilon^{3-c}}\log\frac1\delta$ samples force $\ge\frac{C\min\{c,1\}}{\varepsilon^3}\log\frac1\varepsilon\log\frac1\delta$ expected queries
-- statement:
--   **Theorem 11.** There is an absolute constant $C>0$ such that for every constant $c>0$ there is a threshold $\varepsilon_0\in(0,1)$ with the following property. Fix $0<\delta\le1/4$ and $0<\varepsilon\le\varepsilon_0$. If a learning algorithm is $(\varepsilon,\delta)$-PAC for quasi-regular distributions and draws at most
--   $$
--   \frac{C}{\varepsilon^{3-c}}\log\frac1\delta
--   $$
--   value samples on every execution, then there is a quasi-regular distribution $F$ on which
--   $$
--   \mathbb E_F[T]\ \ge\ \frac{C\min\{c,1\}}{\varepsilon^{3}}\log\frac1\varepsilon\log\frac1\delta .
--   $$
--   Any polynomial saving in the sample budget below $\varepsilon^{-3}$ thus costs the $\log(1/\varepsilon)$ factor of the single-sample query bound (Theorem 3), so that bound is tight for quasi-regular distributions.
--
--   **Formalization Note** $C$ is chosen before $c$; $\varepsilon_0$ depends on $c$ only and is chosen before $\delta$, $\varepsilon$ and the learner. $\varepsilon^{3-c}$ is the real power. The sample budget holds for every seed and every value stream; the expectation is the lower integral of the query count in $[0,\infty]$.
--
--   Differences from the source:
--   - generalization: learners that terminate (at termination the algorithm outputs a price) → learners that may fail to stop; a run that never stops fails the PAC event; no termination hypothesis; reason: for learners that terminate almost surely the PAC condition is the source's, so the statement specializes to the source
--   - generalization: learners choose query prices $p_t\ge0$ → learners may query and output any real price; reason: a larger class of learners; a query at $p\le0$ is answered $1$ almost surely, so the class contains every learner of §2.2
--   - encoding: randomized adaptive learner of §2.2 → a measurable action rule of a uniform seed and the past observations, run on an i.i.d. value stream; reason: one uniform seed generates any internal randomization; same learners
--   - encoding: expectations of the counts → lower Lebesgue integrals of $\mathbb N\cup\{\infty\}$-valued counts, in $[0,\infty]$; reason: no integrability condition is needed; the value is $+\infty$ when the expectation is infinite
--   - encoding: quasi-regular distributions (on $[0,\infty)$, with finite optimal revenue) → probability measures on $\mathbb R$ with no mass on $(-\infty,0)$, quasi-regular, $r^*<\infty$; reason: the standing assumptions of §2.1–2.2
--   - reading: 'sufficiently small $\varepsilon>0$' (after 'Fix a constant $c>0$, $0<\delta\le1/4$') → $\exists\,\varepsilon_0\in(0,1)$ depending on $c$ only, chosen before $\delta$; the claim holds for all $\varepsilon\in(0,\varepsilon_0]$; reason: the proof's smallness conditions ($L=\lfloor\varepsilon^{-\min\{c,1\}/2}\rfloor\ge4$, $L+1\le K/4$, $\log((L+2)/2)\ge\frac{\min\{c,1\}}4\log\frac1\varepsilon$) involve $c$ only; this is the stronger reading (a threshold that may also depend on $\delta$ is weaker); requiring $\varepsilon_0<1$ loses nothing, since the claim for $\varepsilon_0$ implies it for any smaller threshold
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), Theorem 11, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_QuerySampleRev_Supplement_IsPACFor
import Definitions.Def_QuerySampleRev_Supplement_IsQuasiRegular

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev.Supplement

open QuerySampleRev

/-- **Theorem 11 (Lower Bound for Quasi-Regular Distributions).** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue Maximization* (manuscript, sha256 c31ea3d3…), Theorem 11, p.24 (PDF 26):
"There exists an absolute constant `C > 0` such that the following holds. Fix a constant `c > 0`,
`0 < δ ≤ 1/4`, and sufficiently small `ε > 0`. If an `(ε, δ)`-PAC learning algorithm for quasi-regular
distributions draws at most `(C/ε^{3−c}) log(1/δ)` value samples, then there exists a quasi-regular
distribution on which it makes at least `(C min{c, 1}/ε³) log(1/ε) log(1/δ)` pricing queries in
expectation."

One absolute constant `C > 0` (chosen before `c`); "sufficiently small `ε`" is a threshold `ε₀ ∈ (0, 1)`
depending on `c` only, chosen before `δ`. The sample budget holds on every execution (§2.2); the conclusion
is an expectation (a lower integral in `ℝ≥0∞`) of the number of pricing queries before stopping.

**Formalization Note.** Learners are randomized, adaptive, interleave samples and queries and stop
adaptively; no termination hypothesis is made. `ε^{3−c}` is the real power. -/
theorem theorem_11 :
    ∃ C : ℝ, 0 < C ∧
      ∀ c : ℝ, 0 < c → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
          ∀ L : Learner, IsPACFor IsQuasiRegular L ε δ →
            (∀ ω : Outcome,
              (sampleCount L ω : ℝ≥0∞) ≤ ENNReal.ofReal (C / ε ^ (3 - c) * Real.log (1 / δ))) →
            ∃ μ : Measure ℝ, InFamilyOf IsQuasiRegular μ ∧
              ENNReal.ofReal (C * min c 1 / ε ^ 3 * Real.log (1 / ε) * Real.log (1 / δ)) ≤
                ∫⁻ ω, (queryCount L ω : ℝ≥0∞) ∂lawP μ := by sorry

end QuerySampleRev.Supplement
