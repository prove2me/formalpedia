-- Prove2me | Theorems.Thm_PrivateContinualCounting_Kraft_Supplement_chebyshev_covariance
-- name    : PrivateContinualCounting.Kraft.Supplement.chebyshev_covariance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:30:30.845846+00:00
-- url     : https://prove2.me/theorems/a5242c53-677b-4550-8938-d23aef764dfe
-- title:
--   Lemma 4.1 — Chebyshev covariance bound
-- statement:
--   Let $(N_t)$ be any additive data-independent real noise process with finite second moments on a probability space. Suppose every transcript is $(\varepsilon,\delta)$-DP, where $\varepsilon\ge0$ and $0<\delta<1$. Write $D_i=N_{i+1}-N_i$ and $c=(1-\delta)/(4(1+e^\varepsilon))$. For every finite zero-based window $W$, every $j\in W$ and every real coefficient vector $b$,
--   $$\operatorname{Var}\left(\sum_{i\in W}b_iD_i\right)\ge cb_j^2,\qquad \sum_{i,k\in W}b_i\operatorname{Cov}(D_i,D_k)b_k\ge cb_j^2.$$
--   Thus the covariance matrix dominates $ce_je_j^\top$ in positive semidefinite order. Coefficients may have either sign. This is the privacy-induced variance floor needed by stationarisation.
--
--   Differences from the source:
--   - encoding: positive source time and stream indices → natural times with source input i+1 at coordinate i and zero-time noise zero; reason: the published base conventions are reused and every positive time and interval is retained
--   - generalization: Section 4 also fixes an interval envelope B → the covariance inequality is stated for every additive DP process without an interval envelope; reason: the displayed Lemma 4.1 proof never uses B; every source instance satisfies the stated hypotheses
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 9, PDF p. 11, Lemma 4.1

import Definitions.Def_PrivateContinualCounting_Kraft_Supplement_Covariance

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft.Supplement

/-- Lemma 4.1. The quadratic form is the equivalent covariance PSD bound. -/
theorem chebyshev_covariance {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (N : AdditiveNoise Ω P)
    (ε δ : ℝ) (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hDP : TranscriptDP N.law ε δ) :
    ∀ (W : Finset ℕ) (j : ℕ), j ∈ W → ∀ b : ℕ → ℝ,
      privacyConstant ε δ * (b j)^2 ≤
        variance (fun ω => ∑ i ∈ W, b i * N.increment i ω) P ∧
      privacyConstant ε δ * (b j)^2 ≤
        ∑ i ∈ W, ∑ k ∈ W, b i * covariance (N.increment i) (N.increment k) P * b k := by sorry

end PrivateContinualCounting.Kraft.Supplement
