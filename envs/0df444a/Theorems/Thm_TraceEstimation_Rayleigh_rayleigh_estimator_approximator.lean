-- Prove2me | Theorems.Thm_TraceEstimation_Rayleigh_rayleigh_estimator_approximator
-- name    : TraceEstimation.Rayleigh.rayleigh_estimator_approximator
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:25:32.256989+00:00
-- url     : https://prove2.me/theorems/4b3ee497-487b-40e0-b4ce-c6833ce8534f
-- title:
--   Theorem 6.1 (corrected) — $R_M$ is an $(\epsilon,\delta)$-approximator for $M \ge \frac12\epsilon^{-2}n^2\mathrm{rank}^{-2}(A)\ln(2/\delta)\kappa_f^2(A)$
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be a nonzero symmetric positive semi-definite matrix, and let $\kappa_f(A)$ be the ratio between its largest and smallest nonzero eigenvalue. Let $\epsilon > 0$ and $0 < \delta < 1$. Let $R_M = \frac1M\sum_{i=1}^M z_i^TAz_i$ be a normalized Rayleigh-quotient trace estimator of $A$: $z_1, \ldots, z_M$ are independent random vectors with $z_i^Tz_i = n$ and $\mathrm{E}(z_i^TAz_i) = \mathrm{trace}(A)$. If
--
--   $$M \;\ge\; \frac{\ln(2/\delta)\cdot n^2\,\kappa_f^2(A)}{2\,\mathrm{rank}^2(A)\,\epsilon^2},$$
--
--   then $R_M$ is an $(\epsilon,\delta)$-approximator of $\mathrm{trace}(A)$, that is,
--
--   $$\Pr\bigl(|R_M - \mathrm{trace}(A)| \le \epsilon\,\mathrm{trace}(A)\bigr) \ge 1-\delta .$$
--
--   The bound holds for every estimator in the class at once — Hutchinson's, the unit vector estimator, and any other normalized one — and needs no assumption on the distribution of the $z_i$ beyond normalization and unbiasedness. Its price is the factor $\kappa_f^2(A)$, so it is informative for well-conditioned matrices.
--
--   **Formalization Note** The paper prints the threshold as $M \ge \frac12\epsilon^{-2}n^{-2}\mathrm{rank}^2(A)\ln(2/\delta)\kappa_f^2(A)$ (Theorem 6.1 and Table I); its proof on p. 8:10 ends with $M \ge \ln(2/\delta)\,n^2\kappa_f^2(A)/(2\,\mathrm{rank}^2(A)\epsilon^2)$, with the exponents of $n$ and $\mathrm{rank}(A)$ swapped. The printed version is false: for $n = 2$, $A = e_1e_1^T$, $z = \sqrt2\,e_k$ with $k$ uniform on $\{1,2\}$, and $\epsilon = \delta = 1/2$, it admits $M = 1$, while $R_1 \in \{0, 2\}$ is never within $1/2$ of $\mathrm{trace}(A) = 1$. The statement here is the one the proof establishes. The probabilistic model is a general probability space $(\Omega,P)$ with `IsNormalizedRayleighSample P A z` (measurable, mutually independent, $z_i^Tz_i = n$ almost surely, unbiased for this $A$); the hypotheses are satisfiable (Rademacher vectors, or $\sqrt n\,e_k$ with $k$ uniform). The assumptions $A \ne 0$ and $M \ge 1$ are implicit on the page ($\kappa_f$ and $1/M$ must make sense).
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:10, Theorem 6.1 (threshold as in the last display of its proof)

import Mathlib
import Definitions.Def_TraceEstimation_Shared_IsApproximator
import Definitions.Def_TraceEstimation_Rayleigh_kappaF
import Definitions.Def_TraceEstimation_Rayleigh_rayleighEstimator

namespace TraceEstimation.Rayleigh

open MeasureTheory ProbabilityTheory Matrix

/-- Avron–Toledo, **Theorem 6.1** (p. 8:10), in the form its proof establishes. Let `A ≠ 0` be a
symmetric positive semi-definite `n × n` matrix, `κ_f(A)` the ratio between its largest and
smallest nonzero eigenvalue, `0 < ε`, `0 < δ < 1`, and `R_M` a normalized Rayleigh-quotient trace
estimator of `A` with `M ≥ 1` samples (Definition 3.2). If
`M ≥ ln(2/δ) · n² κ_f²(A) / (2 rank²(A) ε²)`
(the last display of the proof, p. 8:10), then `R_M` is an `(ε, δ)`-approximator of `trace(A)`.

The paper prints the threshold as `½ ε⁻² n⁻² rank²(A) ln(2/δ) κ_f²(A)`, with the exponents of `n`
and `rank(A)` swapped relative to its proof; the printed version is false (`n = 2`,
`A = e₁e₁ᵀ`, `z = √2 e_k` with `k` uniform, `ε = δ = 1/2`, `M = 1`). -/
theorem rayleigh_estimator_approximator {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n M : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (hA0 : A ≠ 0) (hM : 0 < M) (z : Fin M → Ω → Fin n → ℝ)
    (hz : IsNormalizedRayleighSample P A z) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hMbound : Real.log (2 / δ) * (n : ℝ) ^ 2 * kappaF hA.isHermitian ^ 2 /
        (2 * (A.rank : ℝ) ^ 2 * ε ^ 2) ≤ (M : ℝ)) :
    Shared.IsApproximator P (rayleighEstimator A z) A ε δ := by sorry

end TraceEstimation.Rayleigh
