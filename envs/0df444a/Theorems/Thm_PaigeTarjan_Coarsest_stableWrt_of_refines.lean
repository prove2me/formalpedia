-- Prove2me | Theorems.Thm_PaigeTarjan_Coarsest_stableWrt_of_refines
-- name    : PaigeTarjan.Coarsest.stableWrt_of_refines
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:47:25.165387+00:00
-- url     : https://prove2.me/theorems/cd8b0277-0ef0-4666-ac35-389619f30b6b
-- title:
--   Property (1), p. 978 — stability is inherited under refinement
-- statement:
--   Let $E$ be a relation on a finite set $U$, let $P$ and $R$ be partitions of $U$ with $R$ a refinement of $P$, and let $S \subseteq U$. If $P$ is stable with respect to $S$, then so is $R$:
--   $$R \text{ refines } P,\ P \text{ stable w.r.t. } S \implies R \text{ stable w.r.t. } S.$$
--
--   This is why a set, once used as a splitter, can never be used as a splitter again: every later partition refines the one that was made stable with respect to it.
-- source:
--   Paige, Tarjan, Three Partition Refinement Algorithms, SIAM J. Comput. 16 (1987), p. 978, property (1)

import Mathlib
import Definitions.Def_PaigeTarjan_Coarsest_Basic

namespace PaigeTarjan.Coarsest

/-- Property (1), p. 978: stability is inherited under refinement — if `R` is a refinement of
`P` and `P` is stable with respect to a set `S`, then so is `R`. -/
theorem stableWrt_of_refines {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (P R : Finset (Finset U)) (S : Finset U)
    (hP : IsPartition P) (hR : IsPartition R) (hRP : Refines R P)
    (hPS : StableWrt E P S) :
    StableWrt E R S := by sorry

end PaigeTarjan.Coarsest
