-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P07_stateChi_attained
-- name    : QAlgorithms.Papers.Independent.Frontier18.P07.stateChi_attained
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:58:59.310983+00:00
-- url     : https://prove2.me/theorems/122ad26b-0124-45bf-9cf9-abb80407753a
-- title:
--   Corollary 2: attainment of the single-state χ-function
-- statement:
--   Let $\mathcal H$ and, when a channel is present, $\mathcal H^{\prime}$ be separable complex Hilbert spaces. Write $\mathfrak S(\mathcal H)$ for the positive trace-one operators with trace-norm topology, and $\mathcal P$ for its Borel probability measures with weak convergence. For $\pi\in\mathcal P$, let $\bar\rho(\pi)$ denote its barycenter. A channel $\Phi$ is a completely positive trace-preserving linear map on trace-class operators. Entropies and relative entropies below are nonnegative extended quantities in nats. For a constraint set $A$, let $\mathcal P_A=\{\pi:\bar\rho(\pi)\in A\}$, let $\chi_\Phi(\pi)=\int H(\Phi(\rho)\Vert\Phi(\bar\rho(\pi)))\,\pi(d\rho)$, and define $\bar C(\Phi;A)$ initially as the supremum of $\chi_\Phi$ over finite-support measures in $\mathcal P_A$. Define $\chi_\Phi(\rho_0)=\bar C(\Phi;\{\rho_0\})$, a supremum over finite ensembles with exact average $\rho_0$. If $H(\Phi(\rho_0))<\infty$, there exists a Borel ensemble $\pi_0$ with
--
--   $$\bar\rho(\pi_0)=\rho_0,\quad \operatorname{supp}\pi_0\subseteq\operatorname{Extr}\mathfrak S(\mathcal H),\quad \chi_\Phi(\rho_0)=\int H(\Phi(\rho)\Vert\Phi(\rho_0))\,\pi_0(d\rho).$$
--
--   The pure-state support is explicitly permitted by footnote 3. This gives exact-average attainment without a separate arbitrary constraint set.
-- source:
--   Continuous ensembles and the chi-capacity of infinite-dimensional channels, arXiv:quant-ph/0408176v1, PDF p. 10, Corollary 2: attainment of the single-state χ-function

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07

noncomputable section

open MeasureTheory Filter

open scoped ENNReal Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier18.P07

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsBarycenter IsTraceClassChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Corollary 2 and footnote 3, PDF p.10: the single-state chi-supremum
is attained by a pure-state-supported Borel ensemble with exact average rho. -/
theorem stateChi_attained {I J : Type} [Countable I] [Countable J]
    (Phi : Matrix I I ℂ → Matrix J J ℂ) (hPhi : IsTraceClassChannel Phi)
    (rho : State I) (hentropy : extendedEntropyNats (Phi rho.coefficients) < ⊤) :
    ∃ mu : GeneralizedEnsemble I, HasAverage mu rho ∧
      (mu : Measure (State I)).support ⊆ pureStates I ∧
      stateChi Phi rho = relativeIntegral Phi mu rho.coefficients := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P07

end
