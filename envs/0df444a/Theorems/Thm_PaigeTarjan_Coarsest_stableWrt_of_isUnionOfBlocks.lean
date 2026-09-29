-- Prove2me | Theorems.Thm_PaigeTarjan_Coarsest_stableWrt_of_isUnionOfBlocks
-- name    : PaigeTarjan.Coarsest.stableWrt_of_isUnionOfBlocks
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:48:54.510643+00:00
-- url     : https://prove2.me/theorems/bbfa8fd3-6630-4e1e-b286-e0b75aefe964
-- title:
--   §3, p. 979 — a stable partition is stable with respect to any union of its blocks
-- statement:
--   Let $E$ be a relation on a finite set $U$ and let $Q$ be a stable partition of $U$. For every subfamily $T \subseteq Q$ of blocks,
--   $$Q \text{ is stable with respect to } \textstyle\bigcup_{C \in T} C.$$
--
--   This observation is used in the proof of Lemma 2: a set that is a union of blocks of the current partition is also a union of blocks of any stable partition refining it, and so cannot split that partition.
--
--   **Formalization Note** The empty subfamily is allowed; its union is $\emptyset$, whose preimage is empty, so the statement holds for it as well.
-- source:
--   Paige, Tarjan, Three Partition Refinement Algorithms, SIAM J. Comput. 16 (1987), p. 979, §3, first paragraph, last sentence

import Mathlib
import Definitions.Def_PaigeTarjan_Coarsest_Basic

namespace PaigeTarjan.Coarsest

/-- §3, p. 979, end of the first paragraph: a stable partition is stable with respect to the
union of any subset of its blocks. -/
theorem stableWrt_of_isUnionOfBlocks {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (Q : Finset (Finset U))
    (hQ : IsPartition Q) (hstab : Stable E Q) (T : Finset (Finset U)) (hT : T ⊆ Q) :
    StableWrt E Q (T.biUnion id) := by sorry

end PaigeTarjan.Coarsest
