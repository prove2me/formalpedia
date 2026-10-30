-- Prove2me | Theorems.Thm_StatComplexityDMAudit_OnlineEstimation_hellinger_estimation_le_logloss_gap_masked
-- name    : StatComplexityDMAudit.OnlineEstimation.hellinger_estimation_le_logloss_gap_masked
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:06:23.344348+00:00
-- url     : https://prove2.me/theorems/b0d132bc-1577-432b-acd6-38f99f742d6a
-- title:
--   Lemma A.14 (103) — predictable masked Hellinger bound
-- statement:
--   For arbitrary measurable context and outcome spaces, let an online estimator $\widehat g_t$ and experts $(g_{i,t})_{i\in I}$ follow the normalized density protocol with fibrewise sigma-finite dominating kernel $\nu$. Assume realizability at a fixed true index $i^\star$. Let $J_t\in\{0,1\}$ be a measurable function of the preceding history. For every $0<\delta<1$, a measurable event of probability at least $1-\delta$ satisfies
--   $$\sum_{t<T}J_t\mathbb E[D_{\mathrm H}^2(\widehat g_t(x_t),g_{i^\star,t}(x_t))\mid H_{<t}]\le\sum_{t<T}J_t\bigl(\ell_{\log,t}(\widehat g_t)-\ell_{\log,t}(g_{i^\star,t})\bigr)+2\log(1/\delta).$$
--   A zero mask contributes zero even for an infinite loss. The error conditions on the past alone; it averages the random current context. There is no finite-class, bounded-density, support-positivity or independent-context hypothesis.
--
--   This is the predictable-mask clause of Lemma A.14, with its entire conclusion and coefficient 2. Its comparator is the true expert; the goal item (102) instead uses best-expert regret.
--
--   Differences from the source:
--   - encoding: rounds 1 through T → Fin T with round t.val corresponding to source round t.val + 1; reason: the order, preceding histories and finite sums are identical
--   - encoding: the true conditional outcome law given the past and current context → conditional integral identities for every nonnegative jointly measurable test function; reason: this is the integral formulation of Assumption A.1 on the given probability space, without a regular-disintegration assumption
--   - encoding: log loss log(1/g), best-expert infimum, and conditional Hellinger error → EReal losses and infimum, and ENNReal Hellinger integrals and conditional expectations; reason: zero predictions give positive infinity and an unbounded-below expert class gives negative-infinite infimum, without junk real-valued defaults
--   - encoding: a predictable zero-one mask multiplying each summand → a history-measurable Boolean mask and a conditional zero branch; reason: Boolean values represent exactly zero and one; the zero branch avoids indeterminate products with infinite unused losses
--   - encoding: with probability at least 1 - delta → a measurable good event with pointwise validity; reason: the masked true-expert inequality has a measurable success event; no extra restriction is imposed
--   - generalization: a finite online horizon T → all natural horizons including T = 0; reason: empty sums satisfy the same bound; every positive source horizon remains included
-- source:
--   Foster, Kakade, Qian and Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3 (11 July 2023), https://arxiv.org/abs/2112.13487v3, Lemma A.14, equation (103), printed/PDF p. 76; proof §A.3.5, p. 79; setup pp. 75–76.

import Mathlib
import Definitions.Def_StatComplexityDMAudit_OnlineEstimation_Performance

set_option autoImplicit false
open scoped ENNReal NNReal

namespace StatComplexityDMAudit.OnlineEstimation

open MeasureTheory ProbabilityTheory

/-- arXiv:2112.13487v3, Lemma A.14 (103), p. 76. The mask is predictable,
not allowed to select a round after observing its context or outcome. -/
theorem hellinger_estimation_le_logloss_gap_masked {Ω I X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y] {T : ℕ}
    (ν : Kernel X Y) (hν : ∀ x, SigmaFinite (ν x))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (o : Observations Ω X Y T)
    (q : Predictor ν T) (g : I → Predictor ν T) (istar : I)
    (hreal : IsRealizable μ o g istar) (mask : PredictableMask X Y T)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ μ E ∧
      ∀ ω ∈ E, (maskedEstH μ o q g istar mask ω : EReal) ≤
        maskedGap o q g istar mask ω + (2 * Real.log (1 / δ) : ℝ) := by sorry

end StatComplexityDMAudit.OnlineEstimation
