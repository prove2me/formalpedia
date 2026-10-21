-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P15_proposition_I_3_4
-- name    : QAlgorithms.Papers.Independent.Next46.P15.proposition_I_3_4
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:16:16.671323+00:00
-- url     : https://prove2.me/theorems/d7923843-5733-4e02-9b18-4da3ed6a8789
-- title:
--   Local constancy and the tangent map
-- statement:
--   Let $M,N$ be Hausdorff smooth manifolds modeled on Hausdorff locally convex spaces, with Michal–Bastiani smooth chart transitions, and let $f:M\to N$ be smooth. Then
--   $$f\text{ is locally constant}\quad\Longleftrightarrow\quad T_pf=0\text{ for every }p\in M.$$
--   Here $T_pf:T_pM\to T_{f(p)}N$ is the fiber differential. The condition is expressed by the vanishing of the directional derivative of every coordinate representative of $f$ at every point of its chart overlap.
--
--   This criterion detects local constancy without connectedness, paracompactness, or completeness assumptions. The total tangent map retains its base component $f$.
-- source:
--   Towards a Lie theory for locally convex groups, arXiv:1501.06269v1, PDF p. 16, Proposition I.3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P15

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P15

open Set Filter Topology

open scoped BigOperators

universe u v w z

/-- Proposition I.3.4, PDF p.16: local constancy is equivalent to the
vanishing of every tangent fiber map. Both atlases use Bastiani compatibility. -/
theorem proposition_I_3_4
    {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E]
    {F : Type v} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    [LocallyConvexSpace ℝ F] [T2Space F]
    {M : Type w} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    {N : Type z} [TopologicalSpace N] [T2Space N] [ChartedSpace F N]
    (hM : QAlgorithms.Papers.Independent.Claimed50.P22.BastianiAtlas (E := E) (M := M))
    (hN : QAlgorithms.Papers.Independent.Claimed50.P22.BastianiAtlas (E := F) (M := N))
    (f : M → N) (hf : IsMBSmoothBetween (E := E) (F := F) f) :
    IsLocallyConstant f ↔ HasZeroFiberDifferentials (E := E) (F := F) f := by sorry

end QAlgorithms.Papers.Independent.Next46.P15

end
