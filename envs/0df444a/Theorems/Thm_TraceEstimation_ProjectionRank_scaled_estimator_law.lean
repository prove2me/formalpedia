-- Prove2me | Theorems.Thm_TraceEstimation_ProjectionRank_scaled_estimator_law
-- name    : TraceEstimation.ProjectionRank.scaled_estimator_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:13:18.659979+00:00
-- url     : https://prove2.me/theorems/071a4190-49d1-4aa2-aabb-01d06d4218a6
-- title:
--   Lemma 5.3, proof — $MG_M$ is $\chi^2$ with $M\,\mathrm{rank}(A)$ degrees of freedom
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be an orthogonal projection matrix, that is, $A$ is symmetric and $A^2 = A$ (equivalently, $A$ is symmetric with all eigenvalues in $\{0,1\}$). Let $M \ge 1$ and let $G_M$ be the Gaussian trace estimator of $A$ with $M$ samples. Then $M G_M$ has the $\chi^2$ distribution with $M\,\mathrm{rank}(A)$ degrees of freedom: if $g_1, \ldots, g_{M\,\mathrm{rank}(A)}$ are independent standard normal random variables, then
--
--   $$M\,G_M \;\overset{d}{=}\; \sum_{l=1}^{M\,\mathrm{rank}(A)} g_l^2 .$$
--
--   This identifies the exact law of the scaled estimator, reducing every probability bound about $G_M$ for a projection to a tail bound for a $\chi^2$ variable.
--
--   **Formalization Note** No $\chi^2$ distribution is defined. The statement is an equality of pushforward measures (`Measure.map`): the law of $\omega \mapsto M\,G_M(\omega)$ under the product Gaussian measure of Definition 3.1 equals the law of $g \mapsto \sum_l g_l^2$ under the product of $M\,\mathrm{rank}(A)$ standard normals. Both maps are continuous, hence measurable, so neither side is the zero measure that `Measure.map` returns for non-measurable maps. "Projection matrix" is read as orthogonal projection (`A.IsHermitian` and `A * A = A`); an oblique idempotent also has eigenvalues $0$ and $1$, but the paper's diagonalization $A = U^T\mathrm{diag}(1,\ldots,1,0,\ldots,0)U$ with $U$ unitary requires symmetry.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:9, proof of Lemma 5.3, first paragraph

import Mathlib
import Definitions.Def_TraceEstimation_Shared_gaussianEstimator

namespace TraceEstimation.ProjectionRank

open MeasureTheory ProbabilityTheory Matrix

/-- Avron–Toledo, Lemma 5.3, proof (p. 8:9), first paragraph: for an orthogonal projection `A`
(symmetric, `A * A = A`) and `M ≥ 1` samples, `M · G_M` is `χ²` with `M · rank(A)` degrees of
freedom. Stated without a `χ²` definition: the law of `ω ↦ M · G_M(ω)` under the product
Gaussian measure equals the law of `g ↦ ∑_{l=1}^{M·rank(A)} g_l²` for i.i.d. standard normal
`g_1, …, g_{M·rank(A)}`. Both maps are continuous, hence measurable, so neither pushforward is
the junk zero measure. -/
theorem scaled_estimator_law {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA2 : A * A = A) (M : ℕ) (hM : 0 < M) :
    (Shared.gaussianSampleMeasure n M).map (fun ω => (M : ℝ) * Shared.gaussianEstimator A M ω) =
      (Measure.pi fun _ : Fin (M * A.rank) => gaussianReal 0 1).map
        (fun g => ∑ l, g l ^ 2) := by sorry

end TraceEstimation.ProjectionRank
