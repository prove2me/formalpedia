-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P25_iteratedAction_continuity
-- name    : QAlgorithms.Papers.Independent.Next46.P25.iteratedAction_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:01:20.628495+00:00
-- url     : https://prove2.me/theorems/a1c13087-a9af-495d-9756-70c06e78c2c4
-- title:
--   Iterated orbit word maps are separately continuous and Fréchet-jointly continuous
-- statement:
--   Let $\mathbb K\in\{\mathbb R,\mathbb C\}$, let $\mathfrak g$ be a Hausdorff topological Lie algebra over $\mathbb K$ with continuous bracket, and let $V$ be a topological $\mathbb K$-vector space. Suppose the algebraic representation $\rho$ is strongly continuous. For $n\ge1$ and $v\in V$, define
--
--   $$
--   \beta_n^v(x_1,\ldots,x_n)=\rho(x_1)\cdots\rho(x_n)v.
--   $$
--
--   The map $\beta_n^v$ is separately continuous. If, additionally, $\mathfrak g$ is Fréchet, then it is jointly continuous. The operator $\rho(x_n)$ acts first on $v$; continuity of each operator on all of $V$ is not assumed. This transfers strong continuity to all finite ordered word maps.
-- source:
--   On Analytic Vectors for Unitary Representations of Infinite Dimensional Lie Groups, arXiv:1002.4792v2, PDF p. 15, Lemma 4.4

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P25

noncomputable section

open Set Filter Topology

open scoped Classical ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P25

universe u v w z

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Lemma 4.4, PDF p.15: separate continuity in general and joint
    continuity under the additional Frechet hypothesis. -/
theorem iteratedAction_continuity
    {K : Type u} [RCLike K]
    {g : Type v} [LieRing g] [LieAlgebra K g] [UniformSpace g]
    [IsUniformAddGroup g] [T2Space g] [ContinuousSMul K g]
    [Module ℝ g] [IsScalarTower ℝ K g] [ContinuousSMul ℝ g] 
    {V : Type w} [AddCommGroup V] [Module K V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul K V]
    (hBracket : Continuous (fun xy : g × g => ⁅xy.1, xy.2⁆))
    (rho : g →ₗ⁅K⁆ Module.End K V)
    (hStrong : StronglyContinuous (fun x v => rho x v))
    (n : ℕ) (hn : 0 < n) (v : V) :
    SeparatelyContinuous (wordAction (fun x w => rho x w) v n) ∧
    ((LocallyConvexSpace ℝ g ∧ TopologicalSpace.MetrizableSpace g ∧ CompleteSpace g) →
      Continuous (wordAction (fun x w => rho x w) v n)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P25

end
