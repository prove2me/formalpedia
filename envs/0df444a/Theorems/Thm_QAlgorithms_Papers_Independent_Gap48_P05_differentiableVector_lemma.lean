-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P05_differentiableVector_lemma
-- name    : QAlgorithms.Papers.Independent.Gap48.P05.differentiableVector_lemma
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:03:47.012438+00:00
-- url     : https://prove2.me/theorems/de7ddf1c-0671-46c9-8c2b-c5c96b3d0bab
-- title:
--   First differentiability and multilinearity of derived words
-- statement:
--   Let $G$ be a Hausdorff locally convex Lie group with a smooth exponential function, acting jointly continuously by continuous linear automorphisms on an integral-complete Hausdorff locally convex space $V$ over $\mathbb K=\mathbb R$ or $\mathbb C$. Suppose that continuous linear functionals $\alpha$ for which every coefficient $g\mapsto\alpha(\pi(g)v)$ is $C^1$ separate the points of $V$. Write $\mathcal D^n$ for the common domain of all products of $n$ infinitesimal generators and $\omega_v^n(x_1,\ldots,x_n)=d\pi(x_1)\cdots d\pi(x_n)v$. Then
--
--   $$
--   v\in\mathcal D^1,\quad\omega_v^1\text{ continuous}\ \Longrightarrow\ v\in V^1;
--   \qquad
--   n\ge1,\ v\in\mathcal D^n\ \Longrightarrow\ \omega_v^n\text{ is }n\text{-linear}.
--   $$
--
--   Here $V^1$ consists of vectors whose orbit maps are $C^1$. These conclusions separate differentiability from the continuity requirements on iterated derived actions.
-- source:
--   Smoothing operators and $C^*$-algebras for infinite dimensional Lie groups, arXiv:1505.02659v2, PDF p. 5, Lemma 1.1

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

/-- Lemma 1.1, PDF pp. 5--6: both the C^1 conclusion and multilinearity
on D^n. No continuity of omega is assumed in the multilinearity clause. -/
theorem differentiableVector_lemma
    (L : ExponentialLieData E G) (pi : G →* (V ≃L[K] V))
    (hAction : Continuous (fun p : G × V => pi p.1 p.2))
    (hIntegral : IntegralComplete (K := K) (V := V))
    (hSeparate : WeakC1Separates (E := E) (K := K) (fun g v => pi g v)) :
    (∀ v : V, v ∈ DerivedDomain L.exponential (fun g v => pi g v) 1 →
      Continuous (derivedTupleValue L.exponential (fun g v => pi g v) 1 v) →
      BastianiCkMap (E := E) 1 (fun g => pi g v)) ∧
    (∀ n : ℕ, 0 < n → ∀ v : V,
      v ∈ DerivedDomain L.exponential (fun g v => pi g v) n →
      ∃ m : MultilinearMap ℝ (fun _ : Fin n => E) V,
        ∀ xs, m xs = derivedTupleValue L.exponential (fun g v => pi g v) n v xs) := by sorry

end VectorCriteria

end QAlgorithms.Papers.Independent.Gap48.P05
