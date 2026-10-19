-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P07_capacity_all_ensembles
-- name    : QAlgorithms.Papers.Independent.Frontier18.P07.capacity_all_ensembles
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:56:29.986472+00:00
-- url     : https://prove2.me/theorems/ae65f632-f441-4c35-8387-d3268f199009
-- title:
--   Corollary 1: generalized-ensemble capacity formula
-- statement:
--   Let $\mathcal H$ and, when a channel is present, $\mathcal H^{\prime}$ be separable complex Hilbert spaces. Write $\mathfrak S(\mathcal H)$ for the positive trace-one operators with trace-norm topology, and $\mathcal P$ for its Borel probability measures with weak convergence. For $\pi\in\mathcal P$, let $\bar\rho(\pi)$ denote its barycenter. A channel $\Phi$ is a completely positive trace-preserving linear map on trace-class operators. Entropies and relative entropies below are nonnegative extended quantities in nats. For a constraint set $A$, let $\mathcal P_A=\{\pi:\bar\rho(\pi)\in A\}$, let $\chi_\Phi(\pi)=\int H(\Phi(\rho)\Vert\Phi(\bar\rho(\pi)))\,\pi(d\rho)$, and define $\bar C(\Phi;A)$ initially as the supremum of $\chi_\Phi$ over finite-support measures in $\mathcal P_A$. Assume $\bar C(\Phi;A)<\infty$. Then
--
--   $$\bar C(\Phi;A)=\sup_{\pi\in\mathcal P_A}\chi_\Phi(\pi).$$
--
--   The constraint set need not be closed, convex, or nonempty. The empty supremum is zero in $[0,\infty]$. This extends the original finite-ensemble definition to continuous ensembles.
-- source:
--   Continuous ensembles and the chi-capacity of infinite-dimensional channels, arXiv:quant-ph/0408176v1, PDF p. 6, Corollary 1: generalized-ensemble capacity formula

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07

noncomputable section

open MeasureTheory Filter

open scoped ENNReal Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier18.P07

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsBarycenter IsTraceClassChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Corollary 1, PDF p.6: the finite-ensemble capacity equals the supremum
over all Borel ensembles whose average lies in A; A need not be closed or convex. -/
theorem capacity_all_ensembles {I J : Type} [Countable I] [Countable J]
    (Phi : Matrix I I ℂ → Matrix J J ℂ) (hPhi : IsTraceClassChannel Phi)
    (A : Set (State I)) (hfinite : finiteEnsembleCapacity Phi A < ⊤) :
    finiteEnsembleCapacity Phi A = ⨆ mu : {mu : GeneralizedEnsemble I // mu ∈ constrainedEnsembles A},
      ensembleHolevo Phi mu.val := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P07

end
