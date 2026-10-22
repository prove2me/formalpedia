-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P05_differentiableVector_characterization
-- name    : QAlgorithms.Papers.Independent.Gap48.P05.differentiableVector_characterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:04:28.103654+00:00
-- url     : https://prove2.me/theorems/c4ec1f79-a9b1-4dee-8508-a2f41dc34920
-- title:
--   Complete criterion for differentiable vectors
-- statement:
--   Let $G$ act jointly continuously and linearly on an integral-complete Hausdorff locally convex space $V$ over $\mathbb R$ or $\mathbb C$, where $G$ is a Hausdorff locally convex Lie group with a smooth exponential function. Assume that the weak-star $C^1$ functionals separate points, meaning that the continuous functionals with all scalar coefficients $C^1$ separate points of $V$. Let $V^k$ be its $C^k$-vector space, $\mathcal D^k$ the common domain of the products of $k$ generators, and $\omega_v^n$ the ordered derived action. For every positive integer $k$,
--
--   $$
--   v\in V^k\ \Longleftrightarrow\ v\in\mathcal D^k\ \text{and }\omega_v^n\text{ is continuous for every }1\le n\le k.
--   $$
--
--   Also $v\in V^\infty$ if and only if $v\in\mathcal D^\infty$ and every $\omega_v^n$ is continuous. If the Lie algebra is metrizable and Baire and $V$ is metrizable, then
--
--   $$
--   \mathcal D^n=V^n\qquad(n\in\mathbb N\cup\{\infty\}).
--   $$
--
--   This identifies differentiability through generator domains, with continuity automatic under the additional topological assumptions.
-- source:
--   Smoothing operators and $C^*$-algebras for infinite dimensional Lie groups, arXiv:1505.02659v2, PDF p. 6, Theorem 1.1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P05

namespace QAlgorithms.Papers.Independent.Gap48.P05

open Set Filter Topology

open QAlgorithms.Papers.Independent.Claimed50.P22

open QAlgorithms.Papers.Independent.Next46.P35

universe u v w z

attribute [local instance] QAlgorithms.Papers.Independent.Gap48.P05.productCharts

section VectorCriteria

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

variable [hETopAdd : IsTopologicalAddGroup E] [hESmul : ContinuousSMul ℝ E]

variable [hELocConv : LocallyConvexSpace ℝ E] [hET2 : T2Space E]

variable {G : Type v} [Group G] [TopologicalSpace G] [hGT2 : T2Space G]

variable [ChartedSpace E G]

variable {V : Type w} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]

variable [hVTopAdd : IsTopologicalAddGroup V] [hVSmul : ContinuousSMul ℝ V]

variable [hVLocConv : LocallyConvexSpace ℝ V] [hVT2 : T2Space V]

variable {K : Type z} [RCLike K] [Module K V] [hTower : IsScalarTower ℝ K V]

variable [hKSmul : ContinuousSMul K V]

include hETopAdd hESmul hELocConv hET2 hGT2
  hVTopAdd hVSmul hVLocConv hVT2 hTower hKSmul

/-- Theorem 1.1, PDF pp. 6--7: both parts, including infinity.
Metrizability and Baire are additional hypotheses only in part (ii);
continuity of omega is a conclusion there. -/
theorem differentiableVector_characterization
    (L : ExponentialLieData E G) (pi : G →* (V ≃L[K] V))
    (hAction : Continuous (fun p : G × V => pi p.1 p.2))
    (hIntegral : IntegralComplete (K := K) (V := V))
    (hSeparate : WeakC1Separates (E := E) (K := K) (fun g v => pi g v)) :
    (∀ k : ℕ, 0 < k → ∀ v : V, VectorCriterion L (fun g v => pi g v) k v) ∧
    (∀ v : V, v ∈ SmoothVectors (E := E) (fun g v => pi g v) ↔
      v ∈ DerivedInfinity L.exponential (fun g v => pi g v) ∧
      ∀ n : ℕ, 0 < n → Continuous (derivedTupleValue L.exponential (fun g v => pi g v) n v)) ∧
    (TopologicalSpace.MetrizableSpace E → BaireSpace E →
      TopologicalSpace.MetrizableSpace V →
      (∀ n : ℕ, 0 < n → ∀ v : V,
        v ∈ DerivedDomain L.exponential (fun g v => pi g v) n ↔
        BastianiCkMap (E := E) n (fun g => pi g v)) ∧
      (DerivedInfinity L.exponential (fun g v => pi g v) =
        SmoothVectors (E := E) (fun g v => pi g v))) := by sorry

end VectorCriteria

end QAlgorithms.Papers.Independent.Gap48.P05
