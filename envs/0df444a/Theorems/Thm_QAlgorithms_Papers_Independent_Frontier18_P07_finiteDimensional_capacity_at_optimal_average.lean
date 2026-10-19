-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P07_finiteDimensional_capacity_at_optimal_average
-- name    : QAlgorithms.Papers.Independent.Frontier18.P07.finiteDimensional_capacity_at_optimal_average
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:59:33.39137+00:00
-- url     : https://prove2.me/theorems/70e2ce57-e8c4-4325-993f-29ddd1b0a954
-- title:
--   §4, unnumbered finite-dimensional equality (13)
-- statement:
--   Let $\mathcal H$ and, when a channel is present, $\mathcal H^{\prime}$ be separable complex Hilbert spaces. Write $\mathfrak S(\mathcal H)$ for the positive trace-one operators with trace-norm topology, and $\mathcal P$ for its Borel probability measures with weak convergence. For $\pi\in\mathcal P$, let $\bar\rho(\pi)$ denote its barycenter. A channel $\Phi$ is a completely positive trace-preserving linear map on trace-class operators. Entropies and relative entropies below are nonnegative extended quantities in nats. For a constraint set $A$, let $\mathcal P_A=\{\pi:\bar\rho(\pi)\in A\}$, let $\chi_\Phi(\pi)=\int H(\Phi(\rho)\Vert\Phi(\bar\rho(\pi)))\,\pi(d\rho)$, and define $\bar C(\Phi;A)$ initially as the supremum of $\chi_\Phi$ over finite-support measures in $\mathcal P_A$. Assume $A$ is nonempty and compact in trace norm, and $\bar C(\Phi;A)<\infty$. Suppose both Hilbert spaces are finite-dimensional. For every optimal ensemble $\pi$ and its barycenter $\rho_0$,
--
--   $$\bar C(\Phi;A)=\chi_\Phi(\rho_0),\qquad \chi_\Phi(\rho_0)=\bar C(\Phi;\{\rho_0\}).$$
--
--   The premise is attainment by the given ensemble. This identifies its average’s single-state chi-value with constrained capacity.
-- source:
--   Continuous ensembles and the chi-capacity of infinite-dimensional channels, arXiv:quant-ph/0408176v1, PDF p. 10, §4, unnumbered finite-dimensional equality (13)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07

noncomputable section

open MeasureTheory Filter

open scoped ENNReal Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier18.P07

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsBarycenter IsTraceClassChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.10, (13): in finite input and output dimension the capacity is the
single-state ensembleHolevo-value at the average of any optimal ensemble. -/
theorem finiteDimensional_capacity_at_optimal_average {I J : Type}
    [Fintype I] [Fintype J]
    (Phi : Matrix I I ℂ → Matrix J J ℂ) (hPhi : IsTraceClassChannel Phi)
    (A : Set (State I)) (hcompact : IsCompact A) (hne : A.Nonempty)
    (hfinite : finiteEnsembleCapacity Phi A < ⊤) (mu : GeneralizedEnsemble I)
    (hoptimal : IsCapacityAttaining Phi A mu) (rho : State I)
    (haverage : HasAverage mu rho) :
    finiteEnsembleCapacity Phi A = stateChi Phi rho := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P07

end
