-- Prove2me | Theorems.Thm_PaigeTarjan_Coarsest_stableWrt_union
-- name    : PaigeTarjan.Coarsest.stableWrt_union
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:47:55.41019+00:00
-- url     : https://prove2.me/theorems/65fed673-d68e-43cc-87af-788dc525a2f4
-- title:
--   Property (2), p. 978 — stability is inherited under union
-- statement:
--   Let $E$ be a relation on a finite set $U$, let $P$ be a partition of $U$, and let $S, T \subseteq U$. If $P$ is stable with respect to $S$ and with respect to $T$, then
--   $$P \text{ is stable with respect to } S \cup T.$$
--
--   Together with inheritance under refinement, this is one of the two ways in which a partition inherits stability; the improved algorithm relies on it to avoid refining by unions of sets already used.
-- source:
--   Paige, Tarjan, Three Partition Refinement Algorithms, SIAM J. Comput. 16 (1987), p. 978, property (2)

import Mathlib
import Definitions.Def_PaigeTarjan_Coarsest_Basic

namespace PaigeTarjan.Coarsest

/-- Property (2), p. 978: stability is inherited under union — a partition that is stable with
respect to two sets is also stable with respect to their union. -/
theorem stableWrt_union {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (P : Finset (Finset U)) (S T : Finset U)
    (hP : IsPartition P) (hS : StableWrt E P S) (hT : StableWrt E P T) :
    StableWrt E P (S ∪ T) := by sorry

end PaigeTarjan.Coarsest
