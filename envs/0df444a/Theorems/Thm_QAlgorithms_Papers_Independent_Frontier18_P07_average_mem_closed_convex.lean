-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P07_average_mem_closed_convex
-- name    : QAlgorithms.Papers.Independent.Frontier18.P07.average_mem_closed_convex
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:02:31.333927+00:00
-- url     : https://prove2.me/theorems/60fbf056-1b41-4fee-b27c-2694e501fc29
-- title:
--   Appendix A, unnumbered (19): support controls the average
-- statement:
--   Let $\mathcal H$ and, when a channel is present, $\mathcal H^{\prime}$ be separable complex Hilbert spaces. Write $\mathfrak S(\mathcal H)$ for the positive trace-one operators with trace-norm topology, and $\mathcal P$ for its Borel probability measures with weak convergence. For $\pi\in\mathcal P$, let $\bar\rho(\pi)$ denote its barycenter. A channel $\Phi$ is a completely positive trace-preserving linear map on trace-class operators. Entropies and relative entropies below are nonnegative extended quantities in nats. Let $U$ be a trace-norm closed convex subset of the state space. For every Borel ensemble $\pi$,
--
--   $$\operatorname{supp}\pi\subseteq U\quad\Longrightarrow\quad\bar\rho(\pi)\in U.$$
--
--   No compactness assumption is made. The formal conclusion asserts a state in $U$ with the integrable barycenter coefficients, rather than assuming a constructed barycenter as independent data.
-- source:
--   Continuous ensembles and the chi-capacity of infinite-dimensional channels, arXiv:quant-ph/0408176v1, PDF p. 14, Appendix A, unnumbered (19): support controls the average

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07

noncomputable section

open MeasureTheory Filter

open scoped ENNReal Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier18.P07

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsBarycenter IsTraceClassChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Appendix A, PDF p.14, (19): support in a closed convex set forces the
actual average to belong to that set; no compactness is assumed. -/
theorem average_mem_closed_convex {I : Type} [Countable I]
    (mu : GeneralizedEnsemble I) (U : Set (State I)) (hclosed : IsClosed U)
    (hconvex : Convex ℝ (State.coefficients '' U))
    (hsupport : (mu : Measure (State I)).support ⊆ U) :
    ∃ rho ∈ U, HasAverage mu rho := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P07

end
