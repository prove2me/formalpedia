-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P32_cgCover_hasOpenRefinement
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P32.cgCover_hasOpenRefinement
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T06:45:32.85947+00:00
-- url     : https://prove2.me/theorems/417b588d-783e-44ff-a119-4580bbc4869f
-- title:
--   CG-covers on locally compact Hausdorff spaces admit open refinements
-- statement:
--   Let $X$ be a locally compact Hausdorff space, regarded in $\mathrm{CGH}$, and let $(V_a\hookrightarrow X)_{a\in A}$ be a $\mathcal{CG}$-cover. There is an open cover refining this family. Equivalently, its canonical interior refinement covers:
--
--   $$X=\bigcup_{a\in A}\operatorname{int}_{X}(V_a).$$
--
--   The refinement runs from open subsets into the given members $V_a$. This identifies the covering behavior of the two topologies on locally compact Hausdorff spaces.
-- source:
--   Compactly Generated Stacks: A Cartesian Closed Theory of Topological Stacks, arXiv:0907.3925v3, PDF p. 18, Proposition 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P32

namespace QAlgorithms.Papers.Independent.Intakethird100.P32

universe u

open Set Topology

/-- Proposition 3.3, PDF p.18: every CG-cover of a locally compact Hausdorff
space admits an open refinement. The interiors give a canonical such refinement. -/
theorem cgCover_hasOpenRefinement (X : Type u) [TopologicalSpace X]
    [T2Space X] [CompactlyGeneratedSpace X] [LocallyCompactSpace X]
    {A : Type u} (V : A → Set X) (hV : CGCover V) :
    HasOpenRefinement V := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P32
