-- Prove2me | Theorems.Thm_TraceEstimation_ProjectionRank_sample_bound_eq2
-- name    : TraceEstimation.ProjectionRank.sample_bound_eq2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:16:03.91639+00:00
-- url     : https://prove2.me/theorems/82d323fc-2f3c-4405-9aa4-2b376f7cad57
-- title:
--   Lemma 5.3, proof, Eq. (2) — $M \ge 6\,\mathrm{rank}(A)^{-1}\epsilon^{-2}\ln(2/\delta)$ gives failure probability $\le\delta$
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be an orthogonal projection matrix (symmetric with $A^2 = A$) of rank $r = \mathrm{rank}(A) \ge 1$, let $0 < \epsilon \le \tfrac12$ and $\delta > 0$, and let $M \ge 1$ be an integer with
--
--   $$M \ge 6\, r^{-1} \epsilon^{-2} \ln(2/\delta). \qquad (2)$$
--
--   Then the Gaussian trace estimator $G_M$ of $A$ satisfies
--
--   $$\Pr\bigl(|G_M - r| \ge r\epsilon\bigr) \le \delta .$$
--
--   This converts the exponential tail bound into a sample-size requirement; it is the bound into which the proof of Lemma 5.3 substitutes $\epsilon = 1/(2r)$.
--
--   **Formalization Note** The probability is `Measure.real` under the product Gaussian measure of Definition 3.1. The range $0 < \epsilon \le 1/2$ is inherited from the $\chi^2$ tail bound. For $\delta \ge 2$ the right side of (2) is non-positive and the conclusion holds trivially since probabilities are at most $1$; no upper bound on $\delta$ is imposed, matching the paper.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:9, proof of Lemma 5.3, Eq. (2)

import Mathlib
import Definitions.Def_TraceEstimation_Shared_gaussianEstimator

namespace TraceEstimation.ProjectionRank

open MeasureTheory ProbabilityTheory Matrix

/-- Avron–Toledo, Lemma 5.3, proof (p. 8:9), Eq. (2): for an orthogonal projection `A`
(symmetric, `A * A = A`) with `rank(A) ≥ 1`, `0 < ε ≤ 1/2`, `δ > 0` and a number of samples
`M ≥ 1` with `M ≥ 6 rank(A)⁻¹ ε⁻² ln(2/δ)`, we have `Pr(|G_M - rank(A)| ≥ rank(A) ε) ≤ δ`. -/
theorem sample_bound_eq2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA2 : A * A = A) (hr : 0 < A.rank) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (δ : ℝ)
    (hδ : 0 < δ) (M : ℕ) (hM : 0 < M)
    (hMε : 6 * (A.rank : ℝ)⁻¹ * ε⁻¹ ^ 2 * Real.log (2 / δ) ≤ M) :
    (Shared.gaussianSampleMeasure n M).real
        {ω | (A.rank : ℝ) * ε ≤ |Shared.gaussianEstimator A M ω - A.rank|} ≤ δ := by sorry

end TraceEstimation.ProjectionRank
