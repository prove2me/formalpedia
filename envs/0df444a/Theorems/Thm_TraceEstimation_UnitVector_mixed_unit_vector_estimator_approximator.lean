-- Prove2me | Theorems.Thm_TraceEstimation_UnitVector_mixed_unit_vector_estimator_approximator
-- name    : TraceEstimation.UnitVector.mixed_unit_vector_estimator_approximator
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:44:31.63736+00:00
-- url     : https://prove2.me/theorems/74e46faf-bf7b-4ec8-8862-5342a9546020
-- title:
--   Theorem 8.4 — $T_M$ is an $(\epsilon,\delta)$-approximator for $M \ge 2n^2\eta^2\epsilon^{-2}\ln(4/\delta)\ln^2(4n^2/\delta)$
-- statement:
--   Let $n \ge 1$, let $F$ be an orthogonal $n\times n$ seed matrix with $\eta = \max_{i,j}|F_{ij}|^2$, and let $A \in \mathbb{R}^{n\times n}$ be symmetric positive semi-definite. Let $0 < \epsilon$ and $0 < \delta < 1$. If the number of samples $M \ge 1$ satisfies
--
--   $$M \ge 2n^2\eta^2\epsilon^{-2}\ln(4/\delta)\ln^2(4n^2/\delta),$$
--
--   then the mixed unit vector estimator
--
--   $$T_M = \frac{n}{M}\sum_{i=1}^{M} z_i^T \mathcal F A \mathcal F^T z_i$$
--
--   is an $(\epsilon,\delta)$-approximator of $\mathrm{trace}(A)$:
--
--   $$\Pr\bigl(|T_M - \mathrm{trace}(A)| \le \epsilon\,\mathrm{trace}(A)\bigr) \ge 1-\delta .$$
--
--   Here $\mathcal F = FD$ with $D$ diagonal with i.i.d. Rademacher entries, and $z_1,\ldots,z_M$ are independent uniform samples from $\{e_1,\ldots,e_n\}$, independent of $D$. For Fourier-type seeds, where $\eta = \Theta(1/n)$, the bound is $O(\epsilon^{-2}\ln(1/\delta)\ln^2(n/\delta))$ samples independently of $A$, each sample requiring only $\lceil\log_2 n\rceil$ random bits (plus the $n$ bits of $D$).
--
--   **Formalization Note** The probability is over the product space of the diagonal $d$ of $D$ and the indices of the $z_i$ (`mixedSampleMeasure n M`). The constant is the one printed in Theorem 8.4, which the proof establishes. The paper's Table I (p. 8:5) lists $8\epsilon^{-2}\ln(4n^2/\delta)\ln(4/\delta)$ for this estimator, which drops the square on $\ln(4n^2/\delta)$ and presumes a specific seed; that entry is not what is stated here.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:13, Theorem 8.4

import Mathlib
import Definitions.Def_TraceEstimation_Shared_IsApproximator
import Definitions.Def_TraceEstimation_UnitVector_mixedUnitVectorEstimator

namespace TraceEstimation.UnitVector

open MeasureTheory ProbabilityTheory Matrix Real

/-- Theorem 8.4 (Avron–Toledo, p. 8:13): let `F` be an orthogonal `n × n` seed matrix (`n ≥ 1`)
with `η = max |F_ij|²`, `A` a symmetric positive semi-definite `n × n` matrix, `0 < ε`,
`0 < δ < 1`, and `M ≥ 1` with `M ≥ 2 n² η² ε⁻² ln(4/δ) ln²(4n²/δ)`. Then the mixed unit vector
estimator `T_M = (n/M) ∑_{i=1}^M z_iᵀ 𝓕 A 𝓕ᵀ z_i` — with `𝓕 = F D`, `D` a diagonal matrix of
i.i.d. Rademacher signs, and `z_1, …, z_M` independent uniform samples from `{e_1, …, e_n}`
drawn independently of `D` — is an `(ε, δ)`-approximator of `trace(A)`. -/
theorem mixed_unit_vector_estimator_approximator {n : ℕ} (hn : 0 < n)
    (F : Matrix (Fin n) (Fin n) ℝ) (hF : Fᵀ * F = 1)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (M : ℕ) (hM : 0 < M)
    (hMbound : 2 * (n : ℝ) ^ 2 * eta F ^ 2 * ε⁻¹ ^ 2 * Real.log (4 / δ) *
        Real.log (4 * (n : ℝ) ^ 2 / δ) ^ 2 ≤ (M : ℝ)) :
    Shared.IsApproximator (mixedSampleMeasure n M) (mixedUnitVectorEstimator F A M) A ε δ := by sorry

end TraceEstimation.UnitVector
