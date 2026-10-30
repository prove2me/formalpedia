-- Prove2me | Theorems.Thm_StatComplexityDMAudit_OnlineEstimation_ville_chernoff_bound
-- name    : StatComplexityDMAudit.OnlineEstimation.ville_chernoff_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:04:52.745203+00:00
-- url     : https://prove2.me/theorems/52eebc4c-ff14-4d1d-a71b-39dcd14e919d
-- title:
--   Lemma A.4 (92) — simultaneous conditional moment bound
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be any probability space, let $(\mathcal F_n)_{n\ge0}$ be a filtration, and let $Z_t$ be real-valued and $\mathcal F_{t+1}$-measurable for $0\le t<T$. For every $0<\delta<1$, a single measurable event $E$ of probability at least $1-\delta$ satisfies, simultaneously for every $0\le n\le T$,
--   $$\sum_{t<n}Z_t\le\sum_{t<n}\log\mathbb E[e^{Z_t}\mid\mathcal F_t]+\log(1/\delta)\quad\text{on }E.$$
--   The conditional nonnegative moments may be infinite; their logarithms take extended-real values, including $\log 0=-\infty$ and $\log(+\infty)=+\infty$. No boundedness, independence or moment-finiteness condition is assumed.
--
--   This is the general filtered-space concentration target used by the high-probability estimation argument. The one good event controls all prefixes, rather than a separate event for each prefix.
--
--   Differences from the source:
--   - encoding: rounds 1 through T → Fin T with round t.val corresponding to source round t.val + 1; reason: the order, preceding histories and finite sums are identical
--   - encoding: conditional exponential moments and their logarithms → nonnegative conditional expectations in ENNReal and logarithms in EReal; reason: this retains infinite conditional moments without a finite-integrability hypothesis
--   - encoding: with probability at least 1 - delta, simultaneously all prefixes → one measurable good event for every prefix; reason: the finite intersection of the measurable prefix inequalities is measurable, so the formulations agree
--   - generalization: a finite online horizon T → all natural horizons including T = 0; reason: empty sums satisfy the same bound; every positive source horizon remains included
-- source:
--   Foster, Kakade, Qian and Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3 (11 July 2023), https://arxiv.org/abs/2112.13487v3, Lemma A.4, equation (92), printed/PDF p. 70, proof pp. 70–71.

import Mathlib

set_option autoImplicit false
open scoped ENNReal NNReal

namespace StatComplexityDMAudit.OnlineEstimation

open MeasureTheory ProbabilityTheory

/-- arXiv:2112.13487v3, Lemma A.4 (92), p. 70. A single measurable event
works for every prefix, including the empty prefix. Exponential moments may be infinite. -/
theorem ville_chernoff_bound {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ)
    (F : Filtration ℕ mΩ) (Z : Fin T → Ω → ℝ)
    (hZ : ∀ t, Measurable[F (t.val + 1)] (Z t))
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ μ E ∧
      ∀ ω ∈ E, ∀ n : ℕ, n ≤ T →
        (∑ t : Fin T, if t.val < n then (Z t ω : EReal) else 0) ≤
          (∑ t : Fin T, if t.val < n then
            ENNReal.log (condLExp (F t.val) μ
              (fun a => ENNReal.ofReal (Real.exp (Z t a))) ω) else 0) +
          (Real.log (1 / δ) : EReal) := by sorry

end StatComplexityDMAudit.OnlineEstimation
