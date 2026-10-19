-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P07_polytope_entropy_continuity_condition
-- name    : QAlgorithms.Papers.Independent.Frontier18.P07.polytope_entropy_continuity_condition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:00:50.371863+00:00
-- url     : https://prove2.me/theorems/656a5deb-de85-4a0f-a2d0-301627e75a1d
-- title:
--   §4 Remark: continuity for finitely many extreme points
-- statement:
--   Let $\mathcal H$ and, when a channel is present, $\mathcal H^{\prime}$ be separable complex Hilbert spaces. Write $\mathfrak S(\mathcal H)$ for the positive trace-one operators with trace-norm topology, and $\mathcal P$ for its Borel probability measures with weak convergence. For $\pi\in\mathcal P$, let $\bar\rho(\pi)$ denote its barycenter. A channel $\Phi$ is a completely positive trace-preserving linear map on trace-class operators. Entropies and relative entropies below are nonnegative extended quantities in nats. For a constraint set $A$, let $\mathcal P_A=\{\pi:\bar\rho(\pi)\in A\}$, let $\chi_\Phi(\pi)=\int H(\Phi(\rho)\Vert\Phi(\bar\rho(\pi)))\,\pi(d\rho)$, and define $\bar C(\Phi;A)$ initially as the supremum of $\chi_\Phi$ over finite-support measures in $\mathcal P_A$. An optimal average is a cluster point in $A$ of the averages of finite ensembles whose Holevo quantities converge to $\bar C(\Phi;A)$. Assume $A$ is nonempty and compact in trace norm, and $\bar C(\Phi;A)<\infty$. Suppose $A$ is convex, has finitely many extreme points, and each extreme point has finite output entropy. Then some optimal average $\rho_0$ satisfies
--
--   $$H(\Phi(\rho_0))<\infty,\qquad H\circ\Phi\text{ is continuous at }\rho_0\text{ relative to }A.$$
--
--   This is the main theorem’s continuity condition. No claim about arbitrary compact convex sets is included.
-- source:
--   Continuous ensembles and the chi-capacity of infinite-dimensional channels, arXiv:quant-ph/0408176v1, PDF p. 10, §4 Remark: continuity for finitely many extreme points

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07

noncomputable section

open MeasureTheory Filter

open scoped ENNReal Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier18.P07

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsBarycenter IsTraceClassChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Remark, PDF p.10: finite-entropy extreme points of a compact polytope
ensure the main theorem's continuity condition at an optimal average. -/
theorem polytope_entropy_continuity_condition {I J : Type}
    [Countable I] [Countable J]
    (Phi : Matrix I I ℂ → Matrix J J ℂ) (hPhi : IsTraceClassChannel Phi)
    (A : Set (State I)) (hcompact : IsCompact A) (hne : A.Nonempty)
    (hfinite : finiteEnsembleCapacity Phi A < ⊤)
    (hconvex : Convex ℝ (State.coefficients '' A))
    (hextreme : ((State.coefficients '' A).extremePoints ℝ).Finite)
    (hentropy : ∀ rho ∈ A,
      rho.coefficients ∈ (State.coefficients '' A).extremePoints ℝ →
        extendedEntropyNats (Phi rho.coefficients) < ⊤) :
    ∃ rho : State I, IsOptimalAverage Phi A rho ∧
      extendedEntropyNats (Phi rho.coefficients) < ⊤ ∧
      ContinuousWithinAt (fun sigma : State I => extendedEntropyNats (Phi sigma.coefficients)) A rho := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P07

end
