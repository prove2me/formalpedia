-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P15_remark_I_5_4
-- name    : QAlgorithms.Papers.Independent.Next46.P15.remark_I_5_4
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:17:51.342051+00:00
-- url     : https://prove2.me/theorems/11f8af98-ca30-477a-b3b4-e20cc473ac6f
-- title:
--   Discontinuous translation on affine functions
-- statement:
--   Let $E$ be an infinite-dimensional Hausdorff real locally convex space, and endow its continuous dual $E'_c$ with the compact-open topology. Identify an affine function $y\mapsto t+\alpha(y)$ with $(t,\alpha)\in\mathbb R\times E'_c$. Translation acts on this space by
--   $$x\cdot(t,\alpha)=(t+\alpha(x),\alpha).$$
--   The action map $E\times(\mathbb R\times E'_c)\to\mathbb R\times E'_c$ is not continuous.
--
--   This affine restriction exhibits the continuity failure of the induced translation representation described in the source. The later stronger assertion concerning every locally convex topology on the full function space is outside this pinned node.
-- source:
--   Towards a Lie theory for locally convex groups, arXiv:1501.06269v1, PDF p. 20, Remark I.5.4 (explicit unnumbered result)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P15

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P15

open Set Filter Topology

open scoped BigOperators

universe u v w z

/-- Remark I.5.4, PDF p.20: translation on affine functions is
discontinuous for infinite-dimensional E with the compact-open dual topology.
The displayed action is x.(t,alpha)=(t+alpha(x),alpha). -/
theorem remark_I_5_4
    {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E]
    (hInfinite : ¬ FiniteDimensional ℝ E) :
    letI : TopologicalSpace (E →L[ℝ] ℝ) := compactDualTopology E
    ¬ Continuous (fun p : E × (ℝ × (E →L[ℝ] ℝ)) =>
      (p.2.1 + p.2.2 p.1, p.2.2)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P15

end
