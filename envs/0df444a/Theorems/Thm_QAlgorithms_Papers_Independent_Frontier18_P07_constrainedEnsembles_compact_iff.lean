-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P07_constrainedEnsembles_compact_iff
-- name    : QAlgorithms.Papers.Independent.Frontier18.P07.constrainedEnsembles_compact_iff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:57:28.603289+00:00
-- url     : https://prove2.me/theorems/1bdf4d2c-b998-4eb2-bbd7-60f5acd0d642
-- title:
--   Proposition 2: compactness of barycenter-constrained measures
-- statement:
--   Let $\mathcal H$ and, when a channel is present, $\mathcal H^{\prime}$ be separable complex Hilbert spaces. Write $\mathfrak S(\mathcal H)$ for the positive trace-one operators with trace-norm topology, and $\mathcal P$ for its Borel probability measures with weak convergence. For $\pi\in\mathcal P$, let $\bar\rho(\pi)$ denote its barycenter. A channel $\Phi$ is a completely positive trace-preserving linear map on trace-class operators. Entropies and relative entropies below are nonnegative extended quantities in nats. For every subset $A\subseteq\mathfrak S(\mathcal H)$, with $\mathcal P_A=\{\pi:\bar\rho(\pi)\in A\}$,
--
--   $$\mathcal P_A\text{ is compact}\quad\Longleftrightarrow\quad A\text{ is compact}.$$
--
--   This includes the empty set and makes no channel or capacity assumption. It connects compact input constraints with compact families of ensembles.
-- source:
--   Continuous ensembles and the chi-capacity of infinite-dimensional channels, arXiv:quant-ph/0408176v1, PDF p. 7, Proposition 2: compactness of barycenter-constrained measures

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07

noncomputable section

open MeasureTheory Filter

open scoped ENNReal Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier18.P07

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsBarycenter IsTraceClassChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 2, PDF p.7: barycenter-constrained laws form a compact set
exactly when the constraint set is compact, including the empty constraint. -/
theorem constrainedEnsembles_compact_iff {I : Type} [Countable I]
    (A : Set (State I)) :
    IsCompact (constrainedEnsembles A) ↔ IsCompact A := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P07

end
