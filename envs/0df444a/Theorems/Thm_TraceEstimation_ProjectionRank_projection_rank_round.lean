-- Prove2me | Theorems.Thm_TraceEstimation_ProjectionRank_projection_rank_round
-- name    : TraceEstimation.ProjectionRank.projection_rank_round
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:17:51.060999+00:00
-- url     : https://prove2.me/theorems/65a6da47-ac1c-4663-883b-29e94e487191
-- title:
--   Lemma 5.3 — rounding $G_M$ recovers $\mathrm{rank}(A)$ of a projection with probability $\ge 1-\delta$ once $M \ge 24\,\mathrm{rank}(A)\ln(2/\delta)$
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be a projection matrix — symmetric, with $A^2 = A$, equivalently symmetric with only the eigenvalues $0$ and $1$ — and let $\delta > 0$ be a failure probability. Let $M \ge 1$ be an integer with
--
--   $$M \ge 24\,\mathrm{rank}(A)\ln(2/\delta),$$
--
--   and let $G_M$ be the Gaussian trace estimator of $A$ with $M$ samples (Definition 3.1). Then
--
--   $$\Pr\bigl(\mathrm{round}(G_M) \ne \mathrm{rank}(A)\bigr) \le \delta .$$
--
--   Thus the rank of a projection available only through matrix–vector products is computed exactly, with failure probability at most $\delta$, from $O(\mathrm{rank}(A)\log(2/\delta))$ products, with no dependence on an accuracy parameter. Computing the rank of a projection is used, for example, to compute charge densities in electronic structure calculations without diagonalization.
--
--   **Formalization Note** "Projection matrix" is formalized as orthogonal projection (`A.IsHermitian` and `A * A = A`), the reading under which the paper's proof, which diagonalizes $A = U^T\mathrm{diag}(1,\ldots,1,0,\ldots,0)U$ with $U$ unitary, applies. $\mathrm{round}$ is Mathlib's `round : ℝ → ℤ`, which rounds half-integers up; the statement does not depend on the tie-breaking rule, since every rounding failure lies in the event $|G_M - \mathrm{rank}(A)| \ge \tfrac12$. The probability is `Measure.real` under the product Gaussian measure of Definition 3.1. No upper bound on $\delta$ is imposed (for $\delta \ge 1$ the statement is trivially true), and the case $\mathrm{rank}(A) = 0$ is included.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:9, Lemma 5.3

import Mathlib
import Definitions.Def_TraceEstimation_Shared_gaussianEstimator

namespace TraceEstimation.ProjectionRank

open MeasureTheory ProbabilityTheory Matrix

/-- Lemma 5.3 (Avron–Toledo, p. 8:9). Let `A ∈ ℝ^{n×n}` be a projection matrix and `δ > 0` a
failure probability. For `M ≥ 24 rank(A) ln(2/δ)` samples (`M ≥ 1`), the Gaussian trace
estimator `G_M` of `A` satisfies `Pr(round(G_M) ≠ rank(A)) ≤ δ`.

"Projection matrix" is an orthogonal projection: `A` symmetric (`A.IsHermitian`) and idempotent
(`A * A = A`), i.e. symmetric with eigenvalues in `{0, 1}` (the proof diagonalises
`A = Uᵀ diag(1,…,1,0,…,0) U` with `U` unitary). `round` is Mathlib's `round : ℝ → ℤ`
(half-integers round up); the probability is `P.real` under the product Gaussian measure of
Definition 3.1. -/
theorem projection_rank_round {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA2 : A * A = A) (δ : ℝ) (hδ : 0 < δ) (M : ℕ) (hM : 0 < M)
    (hMδ : 24 * (A.rank : ℝ) * Real.log (2 / δ) ≤ M) :
    (Shared.gaussianSampleMeasure n M).real
        {ω | round (Shared.gaussianEstimator A M ω) ≠ (A.rank : ℤ)} ≤ δ := by sorry

end TraceEstimation.ProjectionRank
