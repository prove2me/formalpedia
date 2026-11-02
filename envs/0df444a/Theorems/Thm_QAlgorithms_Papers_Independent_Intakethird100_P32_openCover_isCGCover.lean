-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P32_openCover_isCGCover
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P32.openCover_isCGCover
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:44:18.77165+00:00
-- url     : https://prove2.me/theorems/1631043a-8ecd-4b1c-8eeb-de6097038584
-- title:
--   Open covers are CG-covers
-- statement:
--   Let $X$ be a compactly generated Hausdorff space and $(U_a)_{a\in A}$ a universe-small open cover. Then $(U_a\hookrightarrow X)_{a\in A}$ is a $\mathcal{CG}$-cover. Explicitly, for every compact subset $K\subseteq X$, there is a finite set $J\subseteq A$ such that
--
--   $$K=\bigcup_{a\in J}\operatorname{int}_{K}(K\cap U_a).$$
--
--   This is the inclusion of ordinary open covers into the compactly generated covering families of Definition 3.1.
-- source:
--   Compactly Generated Stacks: A Cartesian Closed Theory of Topological Stacks, arXiv:0907.3925v3, PDF p. 18, Proposition 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P32

namespace QAlgorithms.Papers.Independent.Intakethird100.P32

universe u

open Set Topology

/-- Proposition 3.2, PDF p.18: every open cover of a CGH space is a CG-cover. -/
theorem openCover_isCGCover (X : Type u) [TopologicalSpace X]
    [T2Space X] [CompactlyGeneratedSpace X] {A : Type u} (U : A → Set X)
    (hU : IsOpenCover U) : CGCover U := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P32
