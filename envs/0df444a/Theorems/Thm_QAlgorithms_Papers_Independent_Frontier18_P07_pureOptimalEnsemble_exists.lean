-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P07_pureOptimalEnsemble_exists
-- name    : QAlgorithms.Papers.Independent.Frontier18.P07.pureOptimalEnsemble_exists
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:58:33.163362+00:00
-- url     : https://prove2.me/theorems/c0658c16-3ddc-4e68-9131-49fbb189ba5d
-- title:
--   §4, unnumbered Theorem: pure-state optimal generalized ensemble
-- statement:
--   Let $\mathcal H$ and, when a channel is present, $\mathcal H^{\prime}$ be separable complex Hilbert spaces. Write $\mathfrak S(\mathcal H)$ for the positive trace-one operators with trace-norm topology, and $\mathcal P$ for its Borel probability measures with weak convergence. For $\pi\in\mathcal P$, let $\bar\rho(\pi)$ denote its barycenter. A channel $\Phi$ is a completely positive trace-preserving linear map on trace-class operators. Entropies and relative entropies below are nonnegative extended quantities in nats. For a constraint set $A$, let $\mathcal P_A=\{\pi:\bar\rho(\pi)\in A\}$, let $\chi_\Phi(\pi)=\int H(\Phi(\rho)\Vert\Phi(\bar\rho(\pi)))\,\pi(d\rho)$, and define $\bar C(\Phi;A)$ initially as the supremum of $\chi_\Phi$ over finite-support measures in $\mathcal P_A$. An optimal average is a cluster point in $A$ of the averages of finite ensembles whose Holevo quantities converge to $\bar C(\Phi;A)$. Assume $A$ is nonempty and compact in trace norm, and $\bar C(\Phi;A)<\infty$. Let $\rho_0$ be an optimal average with finite output entropy, and suppose $\rho\mapsto H(\Phi(\rho))$ is continuous at $\rho_0$ relative to $A$. Then there is a Borel ensemble $\pi_*\in\mathcal P_A$ such that
--
--   $$\bar\rho(\pi_*)=\rho_0,\qquad \operatorname{supp}\pi_*\subseteq\operatorname{Extr}\mathfrak S(\mathcal H),$$
--   $$\bar C(\Phi;A)=\chi_\Phi(\pi_*)=\int H(\Phi(\rho)\Vert\Phi(\bar\rho(\pi_*)))\,\pi_*(d\rho).$$
--
--   The continuity is to the finite entropy value; entropy may be infinite at other points of $A$. This gives attainment by a pure-state-supported generalized ensemble.
-- source:
--   Continuous ensembles and the chi-capacity of infinite-dimensional channels, arXiv:quant-ph/0408176v1, PDF p. 8, §4, unnumbered Theorem: pure-state optimal generalized ensemble

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07

noncomputable section

open MeasureTheory Filter

open scoped ENNReal Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier18.P07

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsBarycenter IsTraceClassChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Unnumbered Theorem, PDF pp.8-9: continuity of output entropy at a finite-
extendedEntropyNats optimal average yields a pure-state-supported optimal law with exactly
that average. Extended-valued continuity at infinity is not the hypothesis. -/
theorem pureOptimalEnsemble_exists {I J : Type} [Countable I] [Countable J]
    (Phi : Matrix I I ℂ → Matrix J J ℂ) (hPhi : IsTraceClassChannel Phi)
    (A : Set (State I)) (hcompact : IsCompact A) (hne : A.Nonempty)
    (hfinite : finiteEnsembleCapacity Phi A < ⊤)
    (rho : State I) (hoptimal : IsOptimalAverage Phi A rho)
    (hentropy : extendedEntropyNats (Phi rho.coefficients) < ⊤)
    (hcontinuous : ContinuousWithinAt (fun sigma : State I =>
      extendedEntropyNats (Phi sigma.coefficients)) A rho) :
    ∃ mu : GeneralizedEnsemble I, IsCapacityAttaining Phi A mu ∧ HasAverage mu rho ∧
      (mu : Measure (State I)).support ⊆ pureStates I ∧
      finiteEnsembleCapacity Phi A = ensembleHolevo Phi mu ∧
      ensembleHolevo Phi mu = relativeIntegral Phi mu (averageCoefficients mu) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P07

end
