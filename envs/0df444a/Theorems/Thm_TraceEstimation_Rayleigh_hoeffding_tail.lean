-- Prove2me | Theorems.Thm_TraceEstimation_Rayleigh_hoeffding_tail
-- name    : TraceEstimation.Rayleigh.hoeffding_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:22:52.374967+00:00
-- url     : https://prove2.me/theorems/fd97b6ba-43bc-45a3-87e1-9500bbe44022
-- title:
--   Theorem 6.1, proof — Hoeffding tail bound for $R_M$ at every $t > 0$
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be a nonzero symmetric positive semi-definite matrix, $M \ge 1$, and let $R_M = \frac1M\sum_{i=1}^M z_i^TAz_i$ be a normalized Rayleigh-quotient trace estimator of $A$: $z_1,\ldots,z_M$ are independent random vectors on a probability space with $z_i^Tz_i = n$ almost surely and $\mathrm{E}(z_i^TAz_i) = \mathrm{trace}(A)$. Let $\kappa_f(A)$ be the ratio between the largest and smallest nonzero eigenvalue of $A$. Then for every $t > 0$,
--
--   $$\Pr\bigl(|R_M - \mathrm{trace}(A)| \ge t\bigr) \;\le\; 2\exp\left(-\frac{2M^2\,\mathrm{rank}^2(A)\,t^2}{M\cdot n^2\,\mathrm{trace}^2(A)\,\kappa_f^2(A)}\right).$$
--
--   This is Hoeffding's inequality for the $M$ independent summands $z_i^TAz_i$, each confined to an interval of length $\frac{n}{\mathrm{rank}(A)}\mathrm{trace}(A)\kappa_f(A)$.
--
--   **Formalization Note** The model is a general probability space $(\Omega, P)$ with random vectors `z : Fin M → Ω → Fin n → ℝ` satisfying `IsNormalizedRayleighSample P A z` (measurable, mutually independent, not necessarily identically distributed, normalized almost surely, unbiased for this $A$). The hypotheses are satisfiable, for instance by $z_i = \sqrt n\,e_{k_i}$ with independent uniform indices $k_i$. The denominator is positive under the hypotheses ($M, n, \mathrm{trace}(A), \kappa_f(A) > 0$), so no division by zero occurs.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:10, Section 6, proof of Theorem 6.1, display 3

import Mathlib
import Definitions.Def_TraceEstimation_Rayleigh_kappaF
import Definitions.Def_TraceEstimation_Rayleigh_rayleighEstimator

namespace TraceEstimation.Rayleigh

open MeasureTheory ProbabilityTheory Matrix

/-- Avron–Toledo, proof of Theorem 6.1 (p. 8:10), third display (Hoeffding's inequality): let
`A ≠ 0` be symmetric positive semi-definite and `R_M` a normalized Rayleigh-quotient trace
estimator of `A` with `M ≥ 1` samples (Definition 3.2: independent `z_i` with `z_iᵀz_i = n` a.s.
and `E(z_iᵀAz_i) = trace(A)`). For every `t > 0`,
`Pr(|R_M − trace(A)| ≥ t) ≤ 2 exp(−2M² rank²(A) t² / (M n² trace²(A) κ_f²(A)))`. -/
theorem hoeffding_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n M : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (hA0 : A ≠ 0) (hM : 0 < M)
    (z : Fin M → Ω → Fin n → ℝ) (hz : IsNormalizedRayleighSample P A z) (t : ℝ) (ht : 0 < t) :
    P.real {ω | t ≤ |rayleighEstimator A z ω - A.trace|} ≤
      2 * Real.exp (-(2 * (M : ℝ) ^ 2 * (A.rank : ℝ) ^ 2 * t ^ 2) /
        ((M : ℝ) * (n : ℝ) ^ 2 * A.trace ^ 2 * kappaF hA.isHermitian ^ 2)) := by sorry

end TraceEstimation.Rayleigh
