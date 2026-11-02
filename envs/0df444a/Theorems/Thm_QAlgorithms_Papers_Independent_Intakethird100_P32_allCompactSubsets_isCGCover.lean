-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P32_allCompactSubsets_isCGCover
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P32.allCompactSubsets_isCGCover
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:44:54.211718+00:00
-- url     : https://prove2.me/theorems/483cfef4-fa73-45fd-bf87-cf2eeee344b8
-- title:
--   All compact subsets form a CG-cover
-- statement:
--   Let $X$ be a compactly generated Hausdorff space. Index a family by all compact subsets $K\subseteq X$, with each member the inclusion $K\hookrightarrow X$. Then
--
--   $$\{K\hookrightarrow X\mid K\subseteq X\text{ compact}\}\text{ is a }\mathcal{CG}\text{-cover}.$$
--
--   No exhaustion or countability choice is required. This supplies the compact-subset covering family used throughout the paper, also for the empty space.
-- source:
--   Compactly Generated Stacks: A Cartesian Closed Theory of Topological Stacks, arXiv:0907.3925v3, PDF p. 18, Corollary 3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P32

namespace QAlgorithms.Papers.Independent.Intakethird100.P32

universe u

open Set Topology

/-- Corollary 3.1, PDF p.18: the inclusion family of all compact subsets covers
any CGH space in the CG topology, including the empty space. -/
theorem allCompactSubsets_isCGCover (X : Type u) [TopologicalSpace X]
    [T2Space X] [CompactlyGeneratedSpace X] : CGCover (allCompactSubsets X) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P32
