-- Prove2me | Theorems.Thm_PaigeTarjan_Coarsest_split_comm_coarsest
-- name    : PaigeTarjan.Coarsest.split_comm_coarsest
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:50:13.487987+00:00
-- url     : https://prove2.me/theorems/40021ced-fc57-47f4-8b99-2585e66d3183
-- title:
--   Property (4), p. 978 — split is commutative; split(S, split(Q, P)) is the coarsest refinement stable w.r.t. S and Q
-- statement:
--   Let $E$ be a relation on a finite set $U$, let $P$ be a partition of $U$, and let $S, Q \subseteq U$ be two subsets (here $Q$ is a set, not a partition). Then
--   $$\mathrm{split}\bigl(S, \mathrm{split}(Q, P)\bigr) = \mathrm{split}\bigl(Q, \mathrm{split}(S, P)\bigr),$$
--   and this partition is the coarsest refinement of $P$ stable with respect to both $S$ and $Q$: it is a partition of $U$, it refines $P$, it is stable with respect to $S$ and with respect to $Q$, and every partition that refines $P$ and is stable with respect to both $S$ and $Q$ is a refinement of it.
--
--   This is what makes the update $Q \leftarrow \mathrm{split}(S - B, \mathrm{split}(B, Q))$ of the improved algorithm the right one: it yields the coarsest refinement of $Q$ stable with respect to both $B$ and $S - B$.
-- source:
--   Paige, Tarjan, Three Partition Refinement Algorithms, SIAM J. Comput. 16 (1987), p. 978, property (4)

import Mathlib
import Definitions.Def_PaigeTarjan_Coarsest_Basic

namespace PaigeTarjan.Coarsest

/-- Property (4), p. 978 (here `S` and `Q` are subsets of `U` and `P` is a partition of `U`):
`split` is commutative, `split(S, split(Q, P)) = split(Q, split(S, P))`, and this partition is
the coarsest refinement of `P` stable with respect to both `S` and `Q`. -/
theorem split_comm_coarsest {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (P : Finset (Finset U)) (S Q : Finset U)
    (hP : IsPartition P) :
    split E S (split E Q P) = split E Q (split E S P) ∧
    IsPartition (split E S (split E Q P)) ∧
    Refines (split E S (split E Q P)) P ∧
    StableWrt E (split E S (split E Q P)) S ∧
    StableWrt E (split E S (split E Q P)) Q ∧
    ∀ R : Finset (Finset U), IsPartition R → Refines R P →
      StableWrt E R S → StableWrt E R Q → Refines R (split E S (split E Q P)) := by sorry

end PaigeTarjan.Coarsest
