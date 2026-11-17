-- Prove2me | Theorems.Thm_QuerySampleRev_Supplement_theorem_40
-- name    : QuerySampleRev.Supplement.theorem_40
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:27:31.269168+00:00
-- url     : https://prove2.me/theorems/53e9251d-af5d-4913-abf0-98338906a082
-- title:
--   Theorem 40 — without value samples no finite query budget suffices: an MHR law on $[0,1]$ with $\mathbb P[R_{\mathrm{pr}}(p^A)=0]>1-\eta$
-- statement:
--   **Theorem 40.** Let $T\ge0$ be an integer, let $A$ be a (possibly randomized) learning algorithm that uses no value samples and at most $T$ adaptive pricing queries on every execution, and let $\eta\in(0,1)$. Then there is an absolutely continuous MHR distribution $F$, supported on $[0,1]$, with optimal revenue $r^*>0$, such that
--   $$
--   \mathbb P_{F,A}\big[R_{\mathrm{pr}}(p^A)=0\big]>1-\eta
--   \qquad\text{and}\qquad
--   \mathbb E_{F,A}\big[R_{\mathrm{pr}}(p^A)\big]<\eta\,r^* .
--   $$
--   Consequently, for every $\varepsilon,\delta\in(0,1)$, no algorithm that uses zero value samples and a finite query budget is $(\varepsilon,\delta)$-PAC for the MHR, the regular, the quasi-MHR or the quasi-regular family.
--
--   This is why every upper bound of the paper draws at least one value sample: pricing queries alone cannot locate the scale of the distribution.
--
--   **Formalization Note** "Absolutely continuous" is absolute continuity with respect to Lebesgue measure; "supported on $[0,1]$" is "no mass outside $[0,1]$". The first probability is that of "the learner stops and its output earns revenue $0$" (every such learner stops); the expectation is a lower integral in $[0,\infty]$. The quasi-MHR family is the mission's published one.
--
--   Differences from the source:
--   - generalization: learners choose query prices $p_t\ge0$ → learners may query and output any real price; reason: a larger class of learners; a query at $p\le0$ is answered $1$ almost surely, so the class contains every learner of §2.2
--   - encoding: randomized adaptive learner of §2.2 → a measurable action rule of a uniform seed and the past observations, run on an i.i.d. value stream; reason: one uniform seed generates any internal randomization; same learners
--   - encoding: absolutely continuous, supported on $[0,1]$ → $\mu\ll$ Lebesgue and $\mu(\mathbb R\setminus[0,1])=0$; reason: the standard meaning
--   - encoding: $\mathbb P_{F,A}[R_{\mathrm{pr}}(p^A)=0]$, $\mathbb E_{F,A}[R_{\mathrm{pr}}(p^A)]$ → the run-law probability that the learner stops with an output of revenue $0$; the lower integral of the output's revenue in $[0,\infty]$; reason: learners with no samples and at most $T$ queries stop on every execution, so the stopping clause changes nothing
--   - encoding: 'zero value samples and a finite query budget' → no sample round and at most $T$ query rounds before stopping on every execution, for some $T\in\mathbb N$; reason: §2.2: an upper bound on either count holds on every execution
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), Appendix C, Theorem 40, p.52 (PDF p.54)

import Mathlib
import Definitions.Def_QuerySampleRev_IsPAC
import Definitions.Def_QuerySampleRev_Supplement_IsPACFor
import Definitions.Def_QuerySampleRev_Supplement_IsQuasiRegular
import Definitions.Def_QuerySampleRev_Supplement_IsRegular
import Definitions.Def_QuerySampleRev_Supplement_IsMHR

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev.Supplement

open QuerySampleRev

/-- **Theorem 40 (no learning without value samples).** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue Maximization* (manuscript, sha256 c31ea3d3…), Appendix C, Theorem 40, p.52 (PDF 54):
"For every finite query budget `T ≥ 0`, every possibly randomized learning algorithm `A` that uses no value
samples and at most `T` adaptive pricing queries, and every `η ∈ (0, 1)`, there exists an absolutely
continuous MHR distribution `F`, supported on `[0, 1]` and with optimal revenue `r∗ > 0`, such that
`P_{F,A}[R_pr(p^A) = 0] > 1 − η`. The same distribution satisfies `E_{F,A}[R_pr(p^A)] < ηr∗`. Consequently,
for every `ε, δ ∈ (0, 1)`, no algorithm using zero value samples and a finite query budget is `(ε, δ)`-PAC
for the MHR, regular, quasi-MHR, or quasi-regular family."

Two parts. (1)–(2): for every `T ∈ ℕ`, every learner that makes no sample round and at most `T` query rounds
before stopping on every execution, and every `η ∈ (0, 1)`, there is a probability measure `μ` on `ℝ`,
absolutely continuous with respect to Lebesgue measure, with `μ(ℝ ∖ [0, 1]) = 0`, MHR, with `r∗ > 0`, such
that the run law gives probability `> 1 − η` to "the learner stops and its output earns revenue `0`", and
the expected revenue of the output is `< η r∗`. (3): for every `ε, δ ∈ (0, 1)`, a learner with no sample
round and a finite query budget on every execution is not `(ε, δ)`-PAC for the MHR, regular, quasi-MHR
(published `IsPAC`) or quasi-regular family.

**Formalization Note.** Learners are the published randomized adaptive learners; their bounded counts force
every run to stop. The expected revenue is a lower integral in `ℝ≥0∞`. -/
theorem theorem_40 :
    (∀ T : ℕ, ∀ L : Learner,
      (∀ ω : Outcome, sampleCount L ω = 0 ∧ queryCount L ω ≤ T) →
      ∀ η : ℝ, 0 < η → η < 1 →
        ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ ≪ volume ∧ μ (Set.Icc 0 1)ᶜ = 0 ∧
          IsMHR μ ∧ 0 < rStar μ ∧
          ENNReal.ofReal (1 - η) <
            lawP μ {ω | stopTime L ω < ⊤ ∧ revenue μ (output L ω) = 0} ∧
          ∫⁻ ω, revenue μ (output L ω) ∂lawP μ < ENNReal.ofReal η * rStar μ) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ L : Learner,
      (∃ T : ℕ, ∀ ω : Outcome, sampleCount L ω = 0 ∧ queryCount L ω ≤ T) →
        ¬ IsPACFor IsMHR L ε δ ∧ ¬ IsPACFor IsRegular L ε δ ∧ ¬ IsPAC L ε δ ∧
          ¬ IsPACFor IsQuasiRegular L ε δ) := by sorry

end QuerySampleRev.Supplement
