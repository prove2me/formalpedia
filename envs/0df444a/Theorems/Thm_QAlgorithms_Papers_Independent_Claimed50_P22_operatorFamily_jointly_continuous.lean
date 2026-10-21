-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P22_operatorFamily_jointly_continuous
-- name    : QAlgorithms.Papers.Independent.Claimed50.P22.operatorFamily_jointly_continuous
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:08:42.15346+00:00
-- url     : https://prove2.me/theorems/8fa74954-43d1-4104-a2f3-f1a129b33b2a
-- title:
--   Pointwise continuity implies joint evaluation continuity
-- statement:
--   Let $X$ be a first countable topological space, $F$ a real Fréchet space, and $V$ a Hausdorff topological vector space. Let $\alpha:X\to L(F,V)$ assign a continuous linear map to every point. Suppose $x\mapsto\alpha(x)f$ is continuous for each $f\in F$. Then
--
--   $$\widehat\alpha:X\times F\to V,\qquad (x,f)\mapsto\alpha(x)f$$
--
--   is continuous. This criterion allows a nonnormable range and a nonnormable Fréchet domain.
-- source:
--   On Differentiable Vectors for Representations of Infinite Dimensional Lie Groups, arXiv:1002.1602v3, PDF p. 17, Proposition 5.1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P22

namespace QAlgorithms.Papers.Independent.Claimed50.P22

open Set Filter Topology

universe u v w z

/-- Proposition 5.1, PDF p. 17: pointwise continuity of a family of
continuous linear operators with Frechet domain implies joint continuity.
The range is a Hausdorff topological vector space and need not be normable. -/
theorem operatorFamily_jointly_continuous
    {X : Type u} [TopologicalSpace X] [FirstCountableTopology X]
    {F : Type v} [AddCommGroup F] [Module ℝ F] [UniformSpace F]
    [IsUniformAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
    [T2Space F] [TopologicalSpace.MetrizableSpace F] [CompleteSpace F]
    {V : Type w} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    (alpha : X → (F →L[ℝ] V))
    (hPointwise : ∀ f : F, Continuous (fun x => alpha x f)) :
    Continuous (fun p : X × F => alpha p.1 p.2) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P22
