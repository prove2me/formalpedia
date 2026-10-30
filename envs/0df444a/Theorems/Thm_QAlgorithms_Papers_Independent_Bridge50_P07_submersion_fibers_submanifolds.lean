-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P07_submersion_fibers_submanifolds
-- name    : QAlgorithms.Papers.Independent.Bridge50.P07.submersion_fibers_submanifolds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:14:53.92463+00:00
-- url     : https://prove2.me/theorems/850cbbfd-089c-4e66-bfd9-41ef9ea1aae7
-- title:
--   Fibers of locally convex submersions are submanifolds
-- statement:
--   Let $M$ and $N$ be Hausdorff smooth manifolds modeled on arbitrary Hausdorff locally convex real vector spaces, with smoothness defined by jointly continuous iterated directional derivatives. Let $f:M\to N$ be a smooth submersion: near each point, compatible charts identify $f$ with a continuous linear projection admitting a continuous linear right inverse. Then every fiber, with its induced topology and smooth structure, is an embedded submanifold:
--
--   $$
--   \forall y\in N,\qquad f^{-1}(\{y\})\subseteq M\text{ is a smooth submanifold.}
--   $$
--
--   Empty fibers are included. This result supplies the submanifolds used in the paper's kernel and groupoid constructions.
--
--   **Formalization Note** The conclusion uses the local submanifold chart criterion: in a compatible ambient chart the fiber is an affine slice of a closed vector subspace. Closedness of this local model follows from the Hausdorff target; complementability is not assumed in the conclusion.
-- source:
--   A Smooth Model for the String Group, arXiv:1104.4288v4, PDF p. 26, Corollary A.4

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P07

namespace QAlgorithms.Papers.Independent.Bridge50.P07

open Set

open QAlgorithms.Papers.Independent.Next46.P35

universe u v w z

section LocalGeometry

variable {E : Type u} {F : Type v}

variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

variable {M : Type w} {N : Type z}

variable [TopologicalSpace M] [TopologicalSpace N]

variable [ChartedSpace E M] [ChartedSpace F N]

/-- Corollary A.4, PDF p. 26: every fiber of a submersion of Hausdorff
locally convex Bastiani manifolds is an embedded submanifold. Appendix A,
PDF p. 25 defines submersions by local split projections. Empty fibers
are allowed; no surjectivity or nonemptiness hypothesis is added. -/
theorem submersion_fibers_submanifolds
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    [LocallyConvexSpace ℝ F] [T2Space F]
    [T2Space M] [T2Space N]
    (hM : DirectionalAtlas (E := E) (M := M))
    (hN : DirectionalAtlas (E := F) (M := N))
    (f : M → N) (hf : BastianiSubmersion (E := E) (F := F) f) :
    ∀ y : N, HasSubmanifoldCharts (E := E) {x : M | f x = y} := by sorry

end LocalGeometry

end QAlgorithms.Papers.Independent.Bridge50.P07
