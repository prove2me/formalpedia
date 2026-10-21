-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P25_weaklyContinuous_implies_stronglyContinuous
-- name    : QAlgorithms.Papers.Independent.Next46.P25.weaklyContinuous_implies_stronglyContinuous
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:59:55.206332+00:00
-- url     : https://prove2.me/theorems/d8dcdc32-f343-45b2-b3d4-8aff69526dfd
-- title:
--   Weak continuity with completion separation implies strong continuity
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, let $\mathfrak g$ be a Fréchet topological Lie algebra over $\mathbb K$, and let $V$ be a Hausdorff metrizable locally convex $\mathbb K$-space, not necessarily complete. Let $\rho:\mathfrak g\to\operatorname{End}_{\mathbb K}(V)$ be an algebraic representation. Let $\widehat V$ be the completion and let $E\subseteq\widehat V'$ be a linear subspace separating its points. If every scalar map $x\mapsto\alpha(\rho(x)v)$ is continuous for $\alpha\in E$ and $v\in V$, then
--
--   $$
--   x\longmapsto\rho(x)v\text{ is continuous for every }v\in V.
--   $$
--
--   Continuous functionals on the completion identify with the source's functionals on $V$. The conclusion supplies strong continuity without assuming the individual operators on $V$ are continuous.
-- source:
--   On Analytic Vectors for Unitary Representations of Infinite Dimensional Lie Groups, arXiv:1002.4792v2, PDF p. 14, Lemma 4.2

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P25

noncomputable section

open Set Filter Topology

open scoped Classical ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P25

universe u v w z

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Lemma 4.2, PDF pp.14--15: testing against a subspace of the
    COMPLETION's dual. Its restrictions identify with the source's E in V'.
    No continuity of the operators on V is assumed. -/
theorem weaklyContinuous_implies_stronglyContinuous
    {K : Type u} [RCLike K]
    {g : Type v} [LieRing g] [LieAlgebra K g] [UniformSpace g]
    [IsUniformAddGroup g] [T2Space g] [ContinuousSMul K g]
    [Module ℝ g] [IsScalarTower ℝ K g] [ContinuousSMul ℝ g] [LocallyConvexSpace ℝ g]
    [TopologicalSpace.MetrizableSpace g] [CompleteSpace g]
    {V : Type w} [AddCommGroup V] [Module K V] [UniformSpace V]
    [IsUniformAddGroup V] [T2Space V] [ContinuousSMul K V]
    [Module ℝ V] [IsScalarTower ℝ K V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]
    [TopologicalSpace.MetrizableSpace V]
    (hBracket : Continuous (fun xy : g × g => ⁅xy.1, xy.2⁆))
    (rho : g →ₗ⁅K⁆ Module.End K V) :
    letI : UniformContinuousConstSMul K V :=
      uniformContinuousConstSMul_of_continuousConstSMul K V
    ∀ (E : Submodule K ((UniformSpace.Completion V) →L[K] K))
    (hSeparate : ∀ w : UniformSpace.Completion V,
      (∀ alpha : E, (alpha : (UniformSpace.Completion V) →L[K] K) w = 0) → w = 0)
    (hWeak : ∀ (alpha : E) (v : V), Continuous (fun x : g =>
      (alpha : (UniformSpace.Completion V) →L[K] K)
        ((rho x v : V) : UniformSpace.Completion V))),
    StronglyContinuous (fun x v => rho x v) := by sorry

end QAlgorithms.Papers.Independent.Next46.P25

end
