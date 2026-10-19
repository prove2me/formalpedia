-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P07_optimalEnsemble_iff_maximalDistance
-- name    : QAlgorithms.Papers.Independent.Frontier18.P07.optimalEnsemble_iff_maximalDistance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:01:47.767986+00:00
-- url     : https://prove2.me/theorems/20bffb03-fc15-4fd5-a27a-9f0874716789
-- title:
--   Proposition 4: maximal-distance characterization
-- statement:
--   Let $\mathcal H$ and, when a channel is present, $\mathcal H^{\prime}$ be separable complex Hilbert spaces. Write $\mathfrak S(\mathcal H)$ for the positive trace-one operators with trace-norm topology, and $\mathcal P$ for its Borel probability measures with weak convergence. For $\pi\in\mathcal P$, let $\bar\rho(\pi)$ denote its barycenter. A channel $\Phi$ is a completely positive trace-preserving linear map on trace-class operators. Entropies and relative entropies below are nonnegative extended quantities in nats. For a constraint set $A$, let $\mathcal P_A=\{\pi:\bar\rho(\pi)\in A\}$, let $\chi_\Phi(\pi)=\int H(\Phi(\rho)\Vert\Phi(\bar\rho(\pi)))\,\pi(d\rho)$, and define $\bar C(\Phi;A)$ initially as the supremum of $\chi_\Phi$ over finite-support measures in $\mathcal P_A$. Assume $\bar C(\Phi;A)<\infty$. Assume $A$ is convex and fix $\pi\in\mathcal P_A$. Then $\pi$ is optimal if and only if for every $\mu\in\mathcal P_A$,
--
--   $$\int H(\Phi(\rho)\Vert\Phi(\bar\rho(\pi)))\,\mu(d\rho)\le\int H(\Phi(\rho)\Vert\Phi(\bar\rho(\pi)))\,\pi(d\rho)=\chi_\Phi(\pi).$$
--
--   Compactness is not assumed. The reference output remains $\Phi(\bar\rho(\pi))$ for every competitor. This characterizes optimality by maximal distance.
-- source:
--   Continuous ensembles and the chi-capacity of infinite-dimensional channels, arXiv:quant-ph/0408176v1, PDF p. 12, Proposition 4: maximal-distance characterization

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07

noncomputable section

open MeasureTheory Filter

open scoped ENNReal Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier18.P07

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsBarycenter IsTraceClassChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 4, PDF pp.12-13, (17): maximal-distance characterization
under convex constraints; compactness is not assumed in section 5. -/
theorem optimalEnsemble_iff_maximalDistance {I J : Type}
    [Countable I] [Countable J]
    (Phi : Matrix I I ℂ → Matrix J J ℂ) (hPhi : IsTraceClassChannel Phi)
    (A : Set (State I)) (hfinite : finiteEnsembleCapacity Phi A < ⊤)
    (hconvex : Convex ℝ (State.coefficients '' A))
    (mu : GeneralizedEnsemble I) (hadmissible : mu ∈ constrainedEnsembles A) :
    IsCapacityAttaining Phi A mu ↔
      (∀ nu : GeneralizedEnsemble I, nu ∈ constrainedEnsembles A →
        relativeIntegral Phi nu (averageCoefficients mu) ≤
          relativeIntegral Phi mu (averageCoefficients mu)) ∧
      relativeIntegral Phi mu (averageCoefficients mu) = ensembleHolevo Phi mu := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P07

end
