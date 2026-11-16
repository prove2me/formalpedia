-- Prove2me | Theorems.Thm_PrivateContinualCounting_Kraft_Supplement_stationarisation
-- name    : PrivateContinualCounting.Kraft.Supplement.stationarisation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:31:12.000205+00:00
-- url     : https://prove2.me/theorems/7e66082c-662f-41d6-b365-32cc5b629feb
-- title:
--   Lemma 4.2 — stationary integer kernel with all four properties
-- statement:
--   Let $(N_t)$ be additive data-independent noise with $N_0=0$ almost surely and finite second moments, whose transcript law is $(\varepsilon,\delta)$-DP for $\varepsilon\ge0$, $0<\delta<1$. Let $B$ be any nonnegative function on positive integers such that $\operatorname{Var}(N_{a+w}-N_a)\le B(w)$ for every $a\ge0,w\ge1$. Set $c=(1-\delta)/(4(1+e^\varepsilon))$. There exists one real symmetric kernel $\Gamma$ on all of $\mathbb Z^2$ satisfying
--   $$\Gamma_W\succeq0,\qquad \Gamma(i+1,k+1)=\Gamma(i,k),\qquad \Gamma_W\succeq ce_je_j^\top,$$
--   for every finite integer window $W$ and every $j\in W$, and
--   $$\sum_{i,k=a+1}^{a+w}\Gamma(i,k)\le B(w)\quad(a\in\mathbb Z,\ w\ge1).$$
--   These are all four properties of Lemma 4.2. No monotonicity, doubling or growth assumption on $B$ is used. The conclusion supplies the stationary covariance interface for interpolation.
--
--   Differences from the source:
--   - encoding: positive source time and stream indices → natural times with source input i+1 at coordinate i and zero-time noise zero; reason: the published base conventions are reused and every positive time and interval is retained
--   - encoding: B is defined on positive integers → B is a natural-indexed function used only at positive widths; reason: the value B(0) is unused and arbitrary
--   - encoding: positive semidefinite matrix inequalities → all finite real quadratic-form inequalities; reason: this is exactly the definition of the matrix order
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 9, PDF p. 11, Lemma 4.2

import Definitions.Def_PrivateContinualCounting_Kraft_Supplement_Covariance

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft.Supplement

/-- Lemma 4.2, on all integer windows, for an arbitrary nonnegative B. -/
theorem stationarisation {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (N : AdditiveNoise Ω P)
    (ε δ : ℝ) (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hDP : TranscriptDP N.law ε δ) (B : ℕ → ℝ)
    (hB : ∀ w : ℕ, 0 < w → 0 ≤ B w) (hbound : UniformEnvelope N B) :
    ∃ Γ : Kernel, StationaryEnvelope Γ (privacyConstant ε δ) B := by sorry

end PrivateContinualCounting.Kraft.Supplement
