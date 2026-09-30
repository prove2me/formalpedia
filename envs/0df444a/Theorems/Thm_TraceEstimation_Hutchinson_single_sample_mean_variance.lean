-- Prove2me | Theorems.Thm_TraceEstimation_Hutchinson_single_sample_mean_variance
-- name    : TraceEstimation.Hutchinson.single_sample_mean_variance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:31:29.454725+00:00
-- url     : https://prove2.me/theorems/642d9dd5-ebac-41d6-9d52-4191cfceb528
-- title:
--   Lemma 2.1 (Hutchinson) — $z^TAz$ is unbiased; for symmetric $A$, $\mathrm{Var}(z^TAz) = 2(\|A\|_F^2 - \sum_i A_{ii}^2)$
-- statement:
--   Let $A$ be a real $n\times n$ matrix and let $z \in \mathbb{R}^n$ be a random vector whose entries are independent Rademacher random variables ($\Pr(z_i = \pm1) = 1/2$). Then $z^TAz$ has a finite second moment and is an unbiased estimator of the trace:
--
--   $$\mathrm{E}(z^TAz) = \mathrm{trace}(A).$$
--
--   If moreover $A$ is symmetric, then
--
--   $$\mathrm{Var}(z^TAz) = 2\left(\|A\|_F^2 - \sum_{i=1}^{n} A_{ii}^2\right), \qquad \|A\|_F^2 = \sum_{i=1}^n\sum_{j=1}^n A_{ij}^2 .$$
--
--   The variance measures how much of the matrix's Frobenius "energy" lies off the diagonal. It is the single-sample variance of Hutchinson's estimator; for $M$ samples it is divided by $M$.
--
--   **Formalization Note** The paper states the lemma for an arbitrary $n\times n$ matrix. The mean identity holds for every $A$ and is stated so; the variance formula is false without symmetry ($A = \begin{pmatrix}0&1\\0&0\end{pmatrix}$: $z^TAz = z_1z_2$ has variance $1$, the formula gives $2$), so symmetry is a hypothesis of the variance part only. Square integrability is part of the conclusion, so the Bochner integral and Mathlib's `variance` carry their genuine values. The law of $z$ is `rademacherVectorMeasure n`.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:2, Lemma 2.1 (quoted from Hutchinson 1989)

import Mathlib
import Definitions.Def_TraceEstimation_Hutchinson_hutchinsonEstimator

namespace TraceEstimation.Hutchinson

open MeasureTheory ProbabilityTheory Matrix

/-- Lemma 2.1 (Avron–Toledo, p. 8:2, quoted from Hutchinson 1989). Let `z ∈ ℝⁿ` have i.i.d.
Rademacher entries. For every real `n × n` matrix `A`, the quadratic form `zᵀ A z` is square
integrable and unbiased, `E(zᵀ A z) = trace(A)`. If moreover `A` is symmetric, then
`Var(zᵀ A z) = 2 (‖A‖_F² - ∑_i A_ii²)`, with `‖A‖_F² = ∑_{i,j} A_ij²`.
The paper states the lemma for an arbitrary `n × n` matrix; the variance formula is false
without symmetry (`A = !![0, 1; 0, 0]`: `zᵀ A z = z₁ z₂` has variance `1`, the formula gives
`2`), so the symmetry hypothesis is added to the variance part only. -/
theorem single_sample_mean_variance {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (MemLp (fun z : Fin n → ℝ => z ⬝ᵥ (A *ᵥ z)) 2 (rademacherVectorMeasure n) ∧
      ∫ z, z ⬝ᵥ (A *ᵥ z) ∂(rademacherVectorMeasure n) = A.trace) ∧
    (A.IsSymm →
      variance (fun z : Fin n → ℝ => z ⬝ᵥ (A *ᵥ z)) (rademacherVectorMeasure n) =
        2 * (∑ i, ∑ j, A i j ^ 2 - ∑ i, A i i ^ 2)) := by sorry

end TraceEstimation.Hutchinson
