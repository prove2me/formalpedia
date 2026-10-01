-- Prove2me | Theorems.Thm_TraceEstimation_UnitVector_unit_vector_estimator_mean_variance
-- name    : TraceEstimation.UnitVector.unit_vector_estimator_mean_variance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:37:36.884291+00:00
-- url     : https://prove2.me/theorems/86412bc4-6cc3-4ad7-b057-4992f04f6fc8
-- title:
--   Lemma 8.1 — $U_1$ is unbiased with $\mathrm{Var}(U_1) = n\sum_i A_{ii}^2 - \mathrm{trace}^2(A)$
-- statement:
--   Let $A$ be an $n\times n$ real symmetric matrix with $n \ge 1$, and let $U_1 = n\, z^TAz$ be the single-sample unit vector estimator, where $z$ is drawn uniformly from $\{e_1,\ldots,e_n\}$. Then $U_1$ is an unbiased estimator of $\mathrm{trace}(A)$, and its variance is explicit:
--
--   $$\mathrm{E}(U_1) = \mathrm{trace}(A), \qquad \mathrm{Var}(U_1) = n\sum_{i=1}^{n}A_{ii}^2 - \mathrm{trace}^2(A).$$
--
--   The variance vanishes exactly when all diagonal entries of $A$ are equal, and is large when the diagonal is concentrated on a few entries; this motivates mixing the matrix before sampling.
--
--   **Formalization Note** $U_1$ is `unitVectorEstimator A 1` on the sample space `Fin 1 → Fin n` with the uniform law `indexSampleMeasure n 1`; the expectation is the Bochner integral and the variance is Mathlib's `ProbabilityTheory.variance` (the sample space is finite, so both are the genuine moments).
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:12, Lemma 8.1

import Mathlib
import Definitions.Def_TraceEstimation_UnitVector_unitVectorEstimator

namespace TraceEstimation.UnitVector

open MeasureTheory ProbabilityTheory Matrix

/-- Lemma 8.1 (Avron–Toledo, p. 8:12): for an `n × n` symmetric matrix `A` (`n ≥ 1`), the single
sample unit vector estimator `U_1 = n · zᵀ A z`, with `z` uniform on `{e_1, …, e_n}`, is an
unbiased estimator of `trace(A)`, `E(U_1) = trace(A)`, and
`Var(U_1) = n ∑_{i=1}^n A_ii² - trace²(A)`. -/
theorem unit_vector_estimator_mean_variance {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    (∫ k, unitVectorEstimator A 1 k ∂(indexSampleMeasure n 1)) = A.trace ∧
      variance (unitVectorEstimator A 1) (indexSampleMeasure n 1) =
        (n : ℝ) * ∑ i : Fin n, A i i ^ 2 - A.trace ^ 2 := by sorry

end TraceEstimation.UnitVector
