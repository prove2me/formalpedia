-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P07_finiteSupport_dense_in_fiber
-- name    : QAlgorithms.Papers.Independent.Frontier18.P07.finiteSupport_dense_in_fiber
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:54:37.413977+00:00
-- url     : https://prove2.me/theorems/a78e84d4-8866-406b-8f5a-ec15be966072
-- title:
--   Lemma 1: finite-support density in a fixed-average fiber
-- statement:
--   Let $\mathcal H$ and, when a channel is present, $\mathcal H^{\prime}$ be separable complex Hilbert spaces. Write $\mathfrak S(\mathcal H)$ for the positive trace-one operators with trace-norm topology, and $\mathcal P$ for its Borel probability measures with weak convergence. For $\pi\in\mathcal P$, let $\bar\rho(\pi)$ denote its barycenter. A channel $\Phi$ is a completely positive trace-preserving linear map on trace-class operators. Entropies and relative entropies below are nonnegative extended quantities in nats. For every state $\rho_0$, finite-support laws are dense in the exact barycenter fiber:
--
--   $$\{\pi\in\mathcal P:\bar\rho(\pi)=\rho_0\}\subseteq\overline{\{\pi\in\mathcal P: |\operatorname{supp}\pi|<\infty,\ \bar\rho(\pi)=\rho_0\}}.$$
--
--   Closure is for weak convergence of probability measures. No rank or entropy restriction is imposed on $\rho_0$. This permits approximation without changing the average.
-- source:
--   Continuous ensembles and the chi-capacity of infinite-dimensional channels, arXiv:quant-ph/0408176v1, PDF p. 3, Lemma 1: finite-support density in a fixed-average fiber

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07

noncomputable section

open MeasureTheory Filter

open scoped ENNReal Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier18.P07

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsBarycenter IsTraceClassChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 1, PDF pp.3,14-15: finite-support laws are dense in the exact
barycenter fiber, for every prescribed density operator. -/
theorem finiteSupport_dense_in_fiber {I : Type} [Countable I]
    (rho : State I) (mu : GeneralizedEnsemble I) (hmu : HasAverage mu rho) :
    mu ∈ closure {nu : GeneralizedEnsemble I | HasFiniteSupport nu ∧ HasAverage nu rho} := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P07

end
