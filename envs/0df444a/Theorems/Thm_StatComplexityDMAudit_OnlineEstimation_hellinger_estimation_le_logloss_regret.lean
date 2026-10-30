-- Prove2me | Theorems.Thm_StatComplexityDMAudit_OnlineEstimation_hellinger_estimation_le_logloss_regret
-- name    : StatComplexityDMAudit.OnlineEstimation.hellinger_estimation_le_logloss_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:07:16.122898+00:00
-- url     : https://prove2.me/theorems/dce06360-0d69-44e4-bcff-34622afc6849
-- title:
--   Lemma A.14 (102) — Hellinger error controlled by log-loss regret
-- statement:
--   Let $X,Y$ be arbitrary measurable spaces and let $\nu(dy\mid x)$ be a fibrewise sigma-finite dominating kernel. Consider any finite-horizon online estimator $\widehat g_t$ and arbitrary expert class $(g_{i,t})_{i\in I}$ of finite, normalized, jointly measurable conditional densities chosen from the preceding history. Suppose Assumption A.1 holds for a fixed true expert $i^\star$. Define $\mathrm{Reg}_{\mathrm{KL}}$ by (99) using the pointwise expert infimum and $\mathrm{Est}_{\mathrm H}$ by (100) using conditional expectation given the past alone. For every $0<\delta<1$, there exists a measurable event $E$ with
--   $$\mathbb P(E)\ge1-\delta,\qquad\mathrm{Est}_{\mathrm H}\le\mathrm{Reg}_{\mathrm{KL}}+2\log(1/\delta)\quad\text{everywhere on }E.$$
--   Contexts may be random and adaptive. Densities may vanish; log loss there is $+\infty$. The expert infimum can be $-\infty$ and need not be attained or measurable. Squared Hellinger distance has no factor of $1/2$.
--
--   This is the full-domain high-probability clause (102), with the source's exact coefficient 2 and best-expert regret. The independent expectation clause (101) is not asserted by this item. A measurable good event preserves every expert class and implies the printed success-probability statement whenever that success event is measurable.
--
--   Differences from the source:
--   - encoding: rounds 1 through T → Fin T with round t.val corresponding to source round t.val + 1; reason: the order, preceding histories and finite sums are identical
--   - encoding: the true conditional outcome law given the past and current context → conditional integral identities for every nonnegative jointly measurable test function; reason: this is the integral formulation of Assumption A.1 on the given probability space, without a regular-disintegration assumption
--   - encoding: log loss log(1/g), best-expert infimum, and conditional Hellinger error → EReal losses and infimum, and ENNReal Hellinger integrals and conditional expectations; reason: zero predictions give positive infinity and an unbounded-below expert class gives negative-infinite infimum, without junk real-valued defaults
--   - generalization: the success inequality holds with probability at least 1 - delta → a measurable event E of mass at least 1 - delta on which the inequality holds pointwise; reason: this implies the printed assertion whenever the success event is measurable and imposes no measurability restriction on an arbitrary-index expert infimum
--   - generalization: a finite online horizon T → all natural horizons including T = 0; reason: empty sums satisfy the same bound; every positive source horizon remains included
-- source:
--   Foster, Kakade, Qian and Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3 (11 July 2023), https://arxiv.org/abs/2112.13487v3, Lemma A.14, equation (102), printed/PDF p. 76; setup §A.3.1, equations (99)–(100), pp. 75–76; proof §A.3.5, pp. 78–79.

import Mathlib
import Definitions.Def_StatComplexityDMAudit_OnlineEstimation_Performance

set_option autoImplicit false
open scoped ENNReal NNReal

namespace StatComplexityDMAudit.OnlineEstimation

open MeasureTheory ProbabilityTheory

/-- arXiv:2112.13487v3, Lemma A.14 (102), p. 76, selected high-probability
clause only (the independent expectation clause (101) is outside this mission).
A measurable good event avoids assuming measurability of an arbitrary expert infimum. -/
theorem hellinger_estimation_le_logloss_regret {Ω I X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y] {T : ℕ}
    (ν : Kernel X Y) (hν : ∀ x, SigmaFinite (ν x))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (o : Observations Ω X Y T)
    (q : Predictor ν T) (g : I → Predictor ν T) (istar : I)
    (hreal : IsRealizable μ o g istar)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ μ E ∧
      ∀ ω ∈ E, (estH μ o q g istar ω : EReal) ≤
        regKL o q g ω + (2 * Real.log (1 / δ) : ℝ) := by sorry

end StatComplexityDMAudit.OnlineEstimation
