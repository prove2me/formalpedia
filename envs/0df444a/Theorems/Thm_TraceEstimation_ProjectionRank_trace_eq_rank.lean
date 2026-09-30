-- Prove2me | Theorems.Thm_TraceEstimation_ProjectionRank_trace_eq_rank
-- name    : TraceEstimation.ProjectionRank.trace_eq_rank
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:17:08.253244+00:00
-- url     : https://prove2.me/theorems/73883f44-5a1d-4a5a-a645-b212ab7575f9
-- title:
--   Lemma 5.3, proof — a projection matrix has $\mathrm{trace}(A) = \mathrm{rank}(A)$
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be an orthogonal projection matrix, that is, $A$ is symmetric and $A^2 = A$. Then
--
--   $$\mathrm{trace}(A) = \mathrm{rank}(A).$$
--
--   In particular the trace of a projection is an integer. This is why estimating the trace of a projection to absolute error below $\tfrac12$ determines it exactly by rounding, which is the last step of Lemma 5.3.
--
--   **Formalization Note** "Projection matrix" is read as orthogonal projection (`A.IsHermitian` and `A * A = A`), as elsewhere in the mission. The identity also holds for oblique idempotents, but the mission uses only the symmetric case. The rank is Mathlib's `Matrix.rank`, cast to $\mathbb{R}$.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:9, proof of Lemma 5.3, last paragraph

import Mathlib
import Definitions.Def_TraceEstimation_Shared_gaussianEstimator

namespace TraceEstimation.ProjectionRank

open MeasureTheory ProbabilityTheory Matrix

/-- Avron–Toledo, Lemma 5.3, proof (p. 8:9), last paragraph: a projection matrix has
`trace(A) = rank(A)`. "Projection matrix" is read as an orthogonal projection: `A` symmetric
(`A.IsHermitian`) and idempotent (`A * A = A`), i.e. symmetric with eigenvalues in `{0, 1}`,
which is the form `A = Uᵀ diag(1,…,1,0,…,0) U` the proof uses. -/
theorem trace_eq_rank {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA2 : A * A = A) :
    A.trace = (A.rank : ℝ) := by sorry

end TraceEstimation.ProjectionRank
