-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P07_barycenter_continuous
-- name    : QAlgorithms.Papers.Independent.Frontier18.P07.barycenter_continuous
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:54:08.570038+00:00
-- url     : https://prove2.me/theorems/254c2990-f269-481f-9a52-cca35c64941c
-- title:
--   §2, unnumbered: continuity of the average map
-- statement:
--   Let $\mathcal H$ and, when a channel is present, $\mathcal H^{\prime}$ be separable complex Hilbert spaces. Write $\mathfrak S(\mathcal H)$ for the positive trace-one operators with trace-norm topology, and $\mathcal P$ for its Borel probability measures with weak convergence. For $\pi\in\mathcal P$, let $\bar\rho(\pi)$ denote its barycenter. A channel $\Phi$ is a completely positive trace-preserving linear map on trace-class operators. Entropies and relative entropies below are nonnegative extended quantities in nats. There is a barycenter map $b:\mathcal P\to\mathfrak S(\mathcal H)$, identified by its integrable matrix coefficients, such that
--
--   $$b(\pi)=\bar\rho(\pi),\qquad b\text{ is continuous}.$$
--
--   The range carries the trace-norm topology. This is the continuity used in compactness arguments.
-- source:
--   Continuous ensembles and the chi-capacity of infinite-dimensional channels, arXiv:quant-ph/0408176v1, PDF p. 2, §2, unnumbered: continuity of the average map

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07

noncomputable section

open MeasureTheory Filter

open scoped ENNReal Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier18.P07

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsBarycenter IsTraceClassChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2, section 2: the barycenter map is continuous from weak convergence
of Borel probability laws to trace-norm convergence of states. The graph clause
identifies the map by integrable coefficients, without assuming its continuity. -/
theorem barycenter_continuous {I : Type} [Countable I] :
    ∃ average : GeneralizedEnsemble I → State I,
      (∀ mu, HasAverage mu (average mu)) ∧ Continuous average := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P07

end
