-- Prove2me | Theorems.Thm_Timetabling_StableHalf_closed_extend_iff
-- name    : Timetabling.StableHalf.closed_extend_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:42:37.803729+00:00
-- url     : https://prove2.me/theorems/7c37f82b-96d6-4f85-b4d4-38ca4ad727df
-- title:
--   No need to backtrack beyond the last decision
-- statement:
--   Let $G$ be a graph on the nodes $x_j, \bar x_j$ ($j = 1, \dots, n$) and $a$ a partial assignment closed under implications. Then
--
--   $$
--   G \text{ has a stable transversal} \iff G \text{ has a stable transversal extending } a .
--   $$
--
--   With the milestone *implications are forced*, this shows that when both $x_j$ and $\bar x_j$ fail from a closed assignment, no stable transversal exists at all, so the problem has no timetable.
--
--   Differences from the source:
--   - generalization: the conflict graph of a CT4 instance → any graph on Fin n × Bool; reason: the argument uses only closedness; specializes to the conflict graph
--   - encoding: there was no implication fixing the schedule of any of the yet unscheduled teachers → hypothesis IsClosed G a; reason: closedness is exactly this condition on the assignment fixed so far
--   - encoding: both decisions imply that no timetable can be found, then none exists → the equivalence 'a stable transversal exists iff one extends a'; reason: the page's conclusion follows from it together with propagate_spec; stated as the underlying equivalence, both directions
-- source:
--   de Werra (1985), proof of Proposition 2.4, p. 155, "Let us now show that when decisions x_j and x̄_j have been examined ... Hence the problem itself has no timetable.". D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_StableHalf_IsStableTransversal
import Definitions.Def_Timetabling_StableHalf_IsClosed

namespace Timetabling.StableHalf

/-- **No need to backtrack beyond the last decision.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), proof of Proposition 2.4, p. 155:
"Let us now show that when decisions x_j and x̄_j have been examined and when both imply that no
timetable can be found, then none exists. Indeed there is no need to backtrack to some earlier
decision: [...] So the subproblem containing only tacher t_j and all those who were unscheduled
when x_j and x̄_j were examined has no timetable. Hence the problem itself has no timetable."

Let `G` be a graph on `Fin n × Bool` and `a` a closed partial assignment. Then `G` has a stable
transversal if and only if it has a stable transversal extending `a` (agreeing with `a` on every
assigned pair). -/
theorem closed_extend_iff {n : ℕ} (G : SimpleGraph (Fin n × Bool)) (a : Fin n → Option Bool)
    (ha : IsClosed G a) :
    (∃ c : Fin n → Bool, IsStableTransversal G c) ↔
      ∃ c : Fin n → Bool, IsStableTransversal G c ∧ ∀ j b, a j = some b → c j = b := by sorry

end Timetabling.StableHalf
