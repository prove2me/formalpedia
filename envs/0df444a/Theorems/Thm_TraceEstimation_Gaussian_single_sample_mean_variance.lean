-- Prove2me | Theorems.Thm_TraceEstimation_Gaussian_single_sample_mean_variance
-- name    : TraceEstimation.Gaussian.single_sample_mean_variance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:27:42.021643+00:00
-- url     : https://prove2.me/theorems/3ef72179-de5e-4619-9673-28e364ce59a1
-- title:
--   Lemma 5.1 — $G_1$ is unbiased with variance $2\|A\|_F^2$
-- statement:
--   Let $A$ be an $n \times n$ real symmetric matrix and let $z \in \mathbb{R}^n$ have independent standard normal entries. The single-sample Gaussian estimator $G_1 = z^T A z$ has a finite second moment, is an unbiased estimator of the trace, and its variance is twice the squared Frobenius norm of $A$:
--
--   $$\mathrm{E}(G_1) = \mathrm{trace}(A), \qquad \mathrm{Var}(G_1) = 2\|A\|_F^2 = 2\sum_{i=1}^n\sum_{j=1}^n A_{ij}^2 .$$
--
--   The variance of one sample is the first quality measure the paper compares across estimators (Table I); for $M$ samples it is divided by $M$.
--
--   **Formalization Note** $G_1$ is the estimator of Definition 3.1 with $M = 1$ on its product Gaussian space. Square integrability is part of the conclusion, so the Bochner integral and Mathlib's `variance` (both of which return $0$ on non-integrable input) carry their genuine values. The paper adds after the proof that "the lemma also applies when $A$ is non-symmetric"; that remark is not part of the lemma and is false for the variance (for $A = \begin{pmatrix}0&1\\0&0\end{pmatrix}$, $\mathrm{Var}(z^TAz) = 1 \ne 2\|A\|_F^2$), so the statement keeps the symmetry hypothesis.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:7, Lemma 5.1

import Mathlib
import Definitions.Def_TraceEstimation_Shared_gaussianEstimator

namespace TraceEstimation.Gaussian

open MeasureTheory ProbabilityTheory Matrix

/-- Lemma 5.1 (Avron–Toledo, p. 8:7). For a symmetric `A`, the single-sample Gaussian
estimator `G_1 = zᵀ A z` is square integrable and unbiased, `E(G_1) = trace(A)`, and has
variance `Var(G_1) = 2‖A‖_F² = 2 ∑_{i,j} A_{ij}²`. The paper's remark that the lemma "also
applies when A is non-symmetric" is not part of the lemma and is false for the variance. -/
theorem single_sample_mean_variance {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) :
    MemLp (Shared.gaussianEstimator A 1) 2 (Shared.gaussianSampleMeasure n 1) ∧
    ∫ ω, Shared.gaussianEstimator A 1 ω ∂(Shared.gaussianSampleMeasure n 1) = A.trace ∧
    variance (Shared.gaussianEstimator A 1) (Shared.gaussianSampleMeasure n 1) =
      2 * ∑ i : Fin n, ∑ j : Fin n, A i j ^ 2 := by sorry

end TraceEstimation.Gaussian
