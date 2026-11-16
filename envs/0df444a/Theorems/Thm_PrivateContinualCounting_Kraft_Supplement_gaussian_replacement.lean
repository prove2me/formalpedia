-- Prove2me | Theorems.Thm_PrivateContinualCounting_Kraft_Supplement_gaussian_replacement
-- name    : PrivateContinualCounting.Kraft.Supplement.gaussian_replacement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:32:42.784689+00:00
-- url     : https://prove2.me/theorems/13ebdaed-f9a1-4da7-9c22-0cf67ec14fd5
-- title:
--   Corollary 1.3 — Gaussian replacement for every interval envelope
-- statement:
--   Fix $\varepsilon\ge0$, $0<\delta<1$, and an arbitrary nonnegative envelope $B$ on positive integers. Suppose an additive data-independent $(\varepsilon,\delta)$-DP counter with finite second moments and $N_0=0$ almost surely satisfies $\operatorname{Var}(N_{a+w}-N_a)\le B(w)$ for all $a\ge0,w\ge1$. With $c=(1-\delta)/(4(1+e^\varepsilon))$, there exists one real scalar LTI Gaussian factorization counter with unit-GDP noise $N'$ such that, simultaneously,
--   $$\operatorname{Var}(N'_{a+w}-N'_a)\le\frac{B(w)}c\quad(a\ge0,w\ge1),\qquad v'_t\le\frac{B(t)}c\quad(t\ge1).$$
--   For every admissible $\mu>0$ with $\delta_\mu(\varepsilon)\le\delta$, this same counter released at scale $\Delta/\mu$ is $\mu$-GDP and $(\varepsilon,\delta)$-DP, its interval and prefix variances equal their unit-GDP values divided by $\mu^2$, and both envelopes become
--   $$\frac{B(w)}{c\mu^2},\qquad\frac{B(t)}{c\mu^2}.$$
--   No monotonicity or envelope-class assumption on $B$, and no Gaussianity, stationarity or centering of the original noise, is imposed. The same replacement counter works for every interval and every admissible privacy scale. This is the structural reduction used in Theorem 1.2(a).
--
--   Differences from the source:
--   - encoding: positive source time and stream indices → natural times with source input i+1 at coordinate i and zero-time noise zero; reason: the published base conventions are reused and every positive time and interval is retained
--   - encoding: B on positive integers → a natural-indexed B whose value at zero is unused; reason: every source envelope extends arbitrarily at zero
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 2, PDF p. 4, Corollary 1.3; proof pp. 9-10, 21, PDF pp. 11-12, 23

import Definitions.Def_PrivateContinualCounting_Kraft_Supplement_GenericOuter

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft.Supplement

/-- Corollary 1.3, the same scalar counter for every interval and all privacy rescalings. -/
theorem gaussian_replacement {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (N : AdditiveNoise Ω P)
    (ε δ : ℝ) (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hDP : TranscriptDP N.law ε δ) (B : ℕ → ℝ)
    (hB : ∀ w : ℕ, 0 < w → 0 ≤ B w) (hbound : UniformEnvelope N B) :
    ∃ M : LTICounter 1,
      TranscriptGDP (scalarLaw M.val 1) 1 ∧
      (∀ a w : ℕ, 0 < w →
        scalarIntervalVariance M.val 1 a w ≤ B w / privacyConstant ε δ) ∧
      (∀ t : ℕ, 0 < t → M.val.variance t ≤ B t / privacyConstant ε δ) ∧
      ∀ μ : ℝ, AdmissibleGDP ε δ μ →
        TranscriptGDP (scalarLaw M.val μ) μ ∧ TranscriptDP (scalarLaw M.val μ) ε δ ∧
        (∀ a w : ℕ, 0 < w →
          scalarIntervalVariance M.val μ a w = scalarIntervalVariance M.val 1 a w / μ^2 ∧
          scalarIntervalVariance M.val μ a w ≤ B w / (privacyConstant ε δ * μ^2)) ∧
        (∀ t : ℕ, 0 < t →
          variance (scalarNoise M.val μ t) (gaussianSeed (ℕ × Fin 1)) = M.val.variance t / μ^2 ∧
          variance (scalarNoise M.val μ t) (gaussianSeed (ℕ × Fin 1)) ≤
            B t / (privacyConstant ε δ * μ^2)) := by sorry

end PrivateContinualCounting.Kraft.Supplement
