-- Prove2me | Theorems.Thm_StableMSR_Recovery_DecompositionSearch_exists_progress_bag
-- name    : StableMSR.Recovery.DecompositionSearch.exists_progress_bag
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-14T17:19:04.842121+00:00
-- url     : https://prove2.me/theorems/8c8af577-6320-4d88-b0d9-2cfc988f14f5
-- title:
--   A bounded progress bag for a tight connected region
-- statement:
--   Let a finite tree decomposition have bags of size at most $w+1$. Let $C$ be a nonempty connected vertex set disjoint from $S$, suppose one bag contains $S$, and suppose every vertex of $S$ has a neighbor in $C$. There exists a set $B$ satisfying
--
--   $$S\subseteq B\subseteq S\cup C,\quad |B|\le w+1,\quad B\cap C\ne\varnothing.$$
--
--   Moreover $|S|\le w$ and $|C\setminus B|<|C|$. Thus a rooted tight boundary admits a candidate bag that makes strict recursive progress without increasing the width. This is a structural lemma for constructing a small tree decomposition; it does not assert that the complete search algorithm has been implemented.
-- source:
--   Supporting construction lemma for Prove2Me mission Exact Sum-of-Radii Clustering under Any Constant Stability; derived from the Helly property of subtrees and the canonical tree-decomposition axioms.

import Definitions.Def_SeymourThomas1993_Brambles
import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition
open RobertsonSeymour1986.GM5 StableMSR.Recovery.Havens

theorem StableMSR.Recovery.DecompositionSearch.exists_progress_bag {V T : Type} [DecidableEq V]
    [Fintype T] [DecidableEq T] {G : SimpleGraph V} {tree : SimpleGraph T}
    {bags : T → Finset V} (htd : IsTreeDecomposition G tree bags)
    (S C : Finset V) (w : ℕ) (hC : ConnectedSet G C) (hdisj : Disjoint S C)
    (hroot : ∃ r, S ⊆ bags r) (htouch : ∀ s ∈ S, ∃ c ∈ C, G.Adj s c)
    (hwidth : ∀ t, (bags t).card ≤ w+1) :
    ∃ B : Finset V, S ⊆ B ∧ B ⊆ S ∪ C ∧ B.card ≤ w+1 ∧
      (B ∩ C).Nonempty ∧ S.card ≤ w ∧ (C \ B).card < C.card := by sorry
