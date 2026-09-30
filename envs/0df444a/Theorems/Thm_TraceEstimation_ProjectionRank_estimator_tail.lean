-- Prove2me | Theorems.Thm_TraceEstimation_ProjectionRank_estimator_tail
-- name    : TraceEstimation.ProjectionRank.estimator_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:14:45.105992+00:00
-- url     : https://prove2.me/theorems/3d390dba-3346-49f4-8b3a-b2ba31fa5691
-- title:
--   Lemma 5.3, proof — $\Pr(|G_M-\mathrm{rank}(A)|\ge \mathrm{rank}(A)\epsilon)\le 2\exp(-M\,\mathrm{rank}(A)\epsilon^2/6)$
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be an orthogonal projection matrix (symmetric with $A^2 = A$) of rank $r = \mathrm{rank}(A) \ge 1$, let $M \ge 1$, let $G_M$ be the Gaussian trace estimator of $A$ with $M$ samples, and let $0 < \epsilon \le \tfrac12$. Then
--
--   $$\Pr\bigl(|G_M - r| \ge r\epsilon\bigr) = \Pr\bigl(|MG_M - Mr| \ge Mr\epsilon\bigr) \le 2\exp\!\left(-\frac{M r \epsilon^2}{6}\right).$$
--
--   This is the $\chi^2$ tail bound transferred to the Gaussian estimator of a projection: the relative error of $G_M$ as an estimate of $\mathrm{rank}(A)$ is exponentially unlikely to exceed $\epsilon$ in the product $Mr$.
--
--   **Formalization Note** The probabilities are `Measure.real` of events under the product Gaussian measure of Definition 3.1. The range $0 < \epsilon \le 1/2$ is that of the $\chi^2$ tail bound the paper applies (see the milestone on that bound, where the page states no range and the bound fails for $\epsilon = 1$); the paper uses only $\epsilon = 1/(2r)$. "Projection matrix" is read as orthogonal projection.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:9, proof of Lemma 5.3, display after "By applying this result to MG_M"

import Mathlib
import Definitions.Def_TraceEstimation_Shared_gaussianEstimator

namespace TraceEstimation.ProjectionRank

open MeasureTheory ProbabilityTheory Matrix

/-- Avron–Toledo, Lemma 5.3, proof (p. 8:9), the display after "By applying this result to
`MG_M`": for an orthogonal projection `A` (symmetric, `A * A = A`) with `rank(A) ≥ 1`, `M ≥ 1`
and `0 < ε ≤ 1/2` (the range of the `χ²` tail bound it applies),
`Pr(|G_M - rank(A)| ≥ rank(A) ε) = Pr(|M G_M - M rank(A)| ≥ M rank(A) ε)
  ≤ 2 exp(-M rank(A) ε² / 6)`. -/
theorem estimator_tail {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA2 : A * A = A) (hr : 0 < A.rank) (M : ℕ) (hM : 0 < M) (ε : ℝ) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) :
    (Shared.gaussianSampleMeasure n M).real
        {ω | (A.rank : ℝ) * ε ≤ |Shared.gaussianEstimator A M ω - A.rank|} =
      (Shared.gaussianSampleMeasure n M).real
        {ω | (M : ℝ) * A.rank * ε ≤ |(M : ℝ) * Shared.gaussianEstimator A M ω - (M : ℝ) * A.rank|} ∧
    (Shared.gaussianSampleMeasure n M).real
        {ω | (A.rank : ℝ) * ε ≤ |Shared.gaussianEstimator A M ω - A.rank|} ≤
      2 * Real.exp (-((M : ℝ) * A.rank * ε ^ 2 / 6)) := by sorry

end TraceEstimation.ProjectionRank
