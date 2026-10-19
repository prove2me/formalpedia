-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P07_optimalEnsemble_and_capacity_at_average
-- name    : QAlgorithms.Papers.Independent.Frontier18.P07.optimalEnsemble_and_capacity_at_average
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:59:55.84967+00:00
-- url     : https://prove2.me/theorems/a07ac153-d328-4368-b363-8b2c64c73a03
-- title:
--   Corollary 3: capacity at an optimal average and ensemble existence
-- statement:
--   Let $\mathcal H$ and, when a channel is present, $\mathcal H^{\prime}$ be separable complex Hilbert spaces. Write $\mathfrak S(\mathcal H)$ for the positive trace-one operators with trace-norm topology, and $\mathcal P$ for its Borel probability measures with weak convergence. For $\pi\in\mathcal P$, let $\bar\rho(\pi)$ denote its barycenter. A channel $\Phi$ is a completely positive trace-preserving linear map on trace-class operators. Entropies and relative entropies below are nonnegative extended quantities in nats. For a constraint set $A$, let $\mathcal P_A=\{\pi:\bar\rho(\pi)\in A\}$, let $\chi_\Phi(\pi)=\int H(\Phi(\rho)\Vert\Phi(\bar\rho(\pi)))\,\pi(d\rho)$, and define $\bar C(\Phi;A)$ initially as the supremum of $\chi_\Phi$ over finite-support measures in $\mathcal P_A$. An optimal average is a cluster point in $A$ of the averages of finite ensembles whose Holevo quantities converge to $\bar C(\Phi;A)$. Assume $A$ is nonempty and compact in trace norm, and $\bar C(\Phi;A)<\infty$. Write $\chi_\Phi(\rho)=\bar C(\Phi;\{\rho\})$. Both implications hold:
--
--   $$\begin{aligned} (\exists\text{ optimal generalized ensemble})&\Longrightarrow(\exists\text{ optimal average }\rho:\bar C(\Phi;A)=\chi_\Phi(\rho)),\\ (\exists\text{ optimal average }\rho:\bar C(\Phi;A)=\chi_\Phi(\rho),\ H(\Phi(\rho))<\infty)&\Longrightarrow(\exists\text{ optimal generalized ensemble}).\end{aligned}$$
--
--   Finite output entropy occurs only in the second implication. This relates attainment to the value of the single-state chi-function.
-- source:
--   Continuous ensembles and the chi-capacity of infinite-dimensional channels, arXiv:quant-ph/0408176v1, PDF p. 10, Corollary 3: capacity at an optimal average and ensemble existence

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07

noncomputable section

open MeasureTheory Filter

open scoped ENNReal Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier18.P07

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsBarycenter IsTraceClassChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Corollary 3, PDF p.10: both implications are retained; finite output
extendedEntropyNats is needed only for the implication that produces an optimal ensemble. -/
theorem optimalEnsemble_and_capacity_at_average {I J : Type}
    [Countable I] [Countable J]
    (Phi : Matrix I I ℂ → Matrix J J ℂ) (hPhi : IsTraceClassChannel Phi)
    (A : Set (State I)) (hcompact : IsCompact A) (hne : A.Nonempty)
    (hfinite : finiteEnsembleCapacity Phi A < ⊤) :
    ((∃ mu : GeneralizedEnsemble I, IsCapacityAttaining Phi A mu) →
      ∃ rho : State I, IsOptimalAverage Phi A rho ∧ finiteEnsembleCapacity Phi A = stateChi Phi rho) ∧
    ((∃ rho : State I, IsOptimalAverage Phi A rho ∧
        finiteEnsembleCapacity Phi A = stateChi Phi rho ∧ extendedEntropyNats (Phi rho.coefficients) < ⊤) →
      ∃ mu : GeneralizedEnsemble I, IsCapacityAttaining Phi A mu) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P07

end
