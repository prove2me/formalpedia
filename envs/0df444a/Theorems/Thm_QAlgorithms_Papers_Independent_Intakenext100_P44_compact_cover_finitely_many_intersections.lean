-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P44_compact_cover_finitely_many_intersections
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P44.compact_cover_finitely_many_intersections
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:53:01.172075+00:00
-- url     : https://prove2.me/theorems/df33096d-c823-4624-861b-7293a36f2da1
-- title:
--   A compact member of a locally finite cover meets finitely many others
-- statement:
--   Let $M$ be a topological space and let $(U_i)_{i\in I}$ be a locally finite cover of $M$ by compact subsets, indexed by an arbitrary set $I$. For each fixed $i\in I$,
--
--   $$
--   \{j\in I:U_i\cap U_j\ne\varnothing\}
--   \quad\text{is finite}.
--   $$
--
--   This turns local finiteness into finiteness of all overlap conditions involving one fixed compact member. Neither countability nor Hausdorffness is required.
-- source:
--   Equivalences of Smooth and Continuous Principal Bundles with Infinite-Dimensional Structure Group, arXiv:math/0604142v3, PDF p. 8, Remark II.7: locally finite covers by compact sets

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P44

open Set

open scoped ContDiff

/-- Remark II.7, PDF p. 8: a fixed compact member of a locally finite cover meets
only finitely many other members. The index type and topology are arbitrary, and
no closedness, Hausdorffness, or countability assumption is added. -/
theorem compact_cover_finitely_many_intersections
    {M I : Type*} [TopologicalSpace M] (u : I → Set M)
    (hcover : (⋃ i, u i) = Set.univ) (hcompact : ∀ i, IsCompact (u i))
    (hfinite : LocallyFinite u) (i : I) :
    {j : I | (u i ∩ u j).Nonempty}.Finite := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P44

end
