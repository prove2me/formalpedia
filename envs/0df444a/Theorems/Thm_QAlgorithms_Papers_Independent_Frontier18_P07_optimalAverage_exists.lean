-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P07_optimalAverage_exists
-- name    : QAlgorithms.Papers.Independent.Frontier18.P07.optimalAverage_exists
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:57:55.959972+00:00
-- url     : https://prove2.me/theorems/5e2175c0-e7de-4100-a5f9-cb1ecd4c2abd
-- title:
--   §4, unnumbered: existence of optimal average states
-- statement:
--   Let $\mathcal H$ and, when a channel is present, $\mathcal H^{\prime}$ be separable complex Hilbert spaces. Write $\mathfrak S(\mathcal H)$ for the positive trace-one operators with trace-norm topology, and $\mathcal P$ for its Borel probability measures with weak convergence. For $\pi\in\mathcal P$, let $\bar\rho(\pi)$ denote its barycenter. A channel $\Phi$ is a completely positive trace-preserving linear map on trace-class operators. Entropies and relative entropies below are nonnegative extended quantities in nats. For a constraint set $A$, let $\mathcal P_A=\{\pi:\bar\rho(\pi)\in A\}$, let $\chi_\Phi(\pi)=\int H(\Phi(\rho)\Vert\Phi(\bar\rho(\pi)))\,\pi(d\rho)$, and define $\bar C(\Phi;A)$ initially as the supremum of $\chi_\Phi$ over finite-support measures in $\mathcal P_A$. An optimal average is a cluster point in $A$ of the averages of finite ensembles whose Holevo quantities converge to $\bar C(\Phi;A)$. Assume $A$ is nonempty and compact in trace norm, and $\bar C(\Phi;A)<\infty$. There exists a state $\rho_0$ such that
--
--   $$\rho_0\in A,\qquad \rho_0\text{ is an optimal average}.$$
--
--   This asserts existence of a cluster point of approximating averages; it does not assert attainment by an ensemble.
-- source:
--   Continuous ensembles and the chi-capacity of infinite-dimensional channels, arXiv:quant-ph/0408176v1, PDF p. 8, §4, unnumbered: existence of optimal average states

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07

noncomputable section

open MeasureTheory Filter

open scoped ENNReal Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier18.P07

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsBarycenter IsTraceClassChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.8, section 4: nonempty compact constraints and finite capacity
guarantee an optimal average in the source's cluster-point sense. -/
theorem optimalAverage_exists {I J : Type} [Countable I] [Countable J]
    (Phi : Matrix I I ℂ → Matrix J J ℂ) (hPhi : IsTraceClassChannel Phi)
    (A : Set (State I)) (hcompact : IsCompact A) (hne : A.Nonempty)
    (hfinite : finiteEnsembleCapacity Phi A < ⊤) :
    ∃ rho : State I, IsOptimalAverage Phi A rho := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P07

end
