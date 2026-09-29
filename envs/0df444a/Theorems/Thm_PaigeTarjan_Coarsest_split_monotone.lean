-- Prove2me | Theorems.Thm_PaigeTarjan_Coarsest_split_monotone
-- name    : PaigeTarjan.Coarsest.split_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:48:18.037837+00:00
-- url     : https://prove2.me/theorems/ca4affc5-4e78-453c-99ca-ca8f62f17a5a
-- title:
--   Property (3), p. 978 — split is monotone in its second argument
-- statement:
--   Let $E$ be a relation on a finite set $U$, let $P$ and $Q$ be partitions of $U$ with $P$ a refinement of $Q$, and let $S \subseteq U$. Then
--   $$\mathrm{split}(S, P) \text{ is a refinement of } \mathrm{split}(S, Q).$$
--
--   Monotonicity of $\mathrm{split}$ is the step that carries the invariant of Lemma 2 from one refinement step to the next.
-- source:
--   Paige, Tarjan, Three Partition Refinement Algorithms, SIAM J. Comput. 16 (1987), p. 978, property (3)

import Mathlib
import Definitions.Def_PaigeTarjan_Coarsest_Basic

namespace PaigeTarjan.Coarsest

/-- Property (3), p. 978: `split` is monotone in its second argument — if `S ⊆ U` and `P` is a
refinement of `Q`, then `split(S, P)` is a refinement of `split(S, Q)`. -/
theorem split_monotone {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (P Q : Finset (Finset U)) (S : Finset U)
    (hP : IsPartition P) (hQ : IsPartition Q) (hPQ : Refines P Q) :
    Refines (split E S P) (split E S Q) := by sorry

end PaigeTarjan.Coarsest
