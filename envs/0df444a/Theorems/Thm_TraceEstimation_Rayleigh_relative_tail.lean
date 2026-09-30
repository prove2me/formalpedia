-- Prove2me | Theorems.Thm_TraceEstimation_Rayleigh_relative_tail
-- name    : TraceEstimation.Rayleigh.relative_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:24:17.961307+00:00
-- url     : https://prove2.me/theorems/3ed9aad9-f47e-4b0f-b16c-fdc430be674d
-- title:
--   Theorem 6.1, proof — $\Pr(|R_M-\mathrm{trace}(A)| \ge \epsilon\,\mathrm{trace}(A)) \le 2\exp(-2M\mathrm{rank}^2(A)\epsilon^2/(n^2\kappa_f^2(A)))$
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be a nonzero symmetric positive semi-definite matrix, $M \ge 1$, and let $R_M$ be a normalized Rayleigh-quotient trace estimator of $A$ with $M$ samples (independent random vectors $z_i$ with $z_i^Tz_i = n$ almost surely and $\mathrm{E}(z_i^TAz_i) = \mathrm{trace}(A)$). Let $\kappa_f(A)$ be the ratio between the largest and smallest nonzero eigenvalue of $A$. For every $\epsilon > 0$,
--
--   $$\Pr\bigl(|R_M - \mathrm{trace}(A)| \ge \epsilon\,\mathrm{trace}(A)\bigr) \;\le\; 2\exp\left(-\frac{2M\,\mathrm{rank}^2(A)\,\epsilon^2}{n^2\kappa_f^2(A)}\right).$$
--
--   This is the relative-error form of the Hoeffding bound: the right-hand side no longer involves $\mathrm{trace}(A)$, and it decays exponentially in $M$ at a rate governed by $\mathrm{rank}(A)/(n\,\kappa_f(A))$.
--
--   **Formalization Note** Same probabilistic model as the preceding milestone (`IsNormalizedRayleighSample`). The denominator $n^2\kappa_f^2(A)$ is positive because $A \ne 0$.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:10, Section 6, proof of Theorem 6.1, display 4

import Mathlib
import Definitions.Def_TraceEstimation_Rayleigh_kappaF
import Definitions.Def_TraceEstimation_Rayleigh_rayleighEstimator

namespace TraceEstimation.Rayleigh

open MeasureTheory ProbabilityTheory Matrix

/-- Avron–Toledo, proof of Theorem 6.1 (p. 8:10), fourth display (the Hoeffding bound at
`t = ε trace(A)`): let `A ≠ 0` be symmetric positive semi-definite and `R_M` a normalized
Rayleigh-quotient trace estimator of `A` with `M ≥ 1` samples. For every `ε > 0`,
`Pr(|R_M − trace(A)| ≥ ε trace(A)) ≤ 2 exp(−2M rank²(A) ε² / (n² κ_f²(A)))`. -/
theorem relative_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n M : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (hA0 : A ≠ 0) (hM : 0 < M)
    (z : Fin M → Ω → Fin n → ℝ) (hz : IsNormalizedRayleighSample P A z) (ε : ℝ) (hε : 0 < ε) :
    P.real {ω | ε * A.trace ≤ |rayleighEstimator A z ω - A.trace|} ≤
      2 * Real.exp (-(2 * (M : ℝ) * (A.rank : ℝ) ^ 2 * ε ^ 2) /
        ((n : ℝ) ^ 2 * kappaF hA.isHermitian ^ 2)) := by sorry

end TraceEstimation.Rayleigh
