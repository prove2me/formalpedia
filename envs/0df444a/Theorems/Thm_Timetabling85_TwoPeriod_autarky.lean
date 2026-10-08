-- Prove2me | Theorems.Thm_Timetabling85_TwoPeriod_autarky
-- name    : Timetabling85.TwoPeriod.autarky
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:08.027781+00:00
-- url     : https://prove2.me/theorems/1c4d09be-5432-4991-b5e7-cc2e0ec30202
-- title:
--   Proof of Proposition 2.4, p. 155 — no need to backtrack beyond the last decision
-- statement:
--   Let $G$ be a graph on the nodes $x_j=(j,\mathrm{true})$, $\bar x_j=(j,\mathrm{false})$ of $n$ teachers in which $x_j$ and $\bar x_j$ are linked for every $j$. Let $A$ be a set of pairwise non-adjacent nodes that is closed under implications, $\mathrm{cl}(A)=A$. Then
--   $$
--   G \text{ has a set of } n \text{ pairwise non-adjacent nodes} \iff G \text{ has such a set containing } A .
--   $$
--
--   This is the argument by which de Werra shows that, once both decisions $x_j$ and $\bar x_j$ for a teacher lead to a contradiction, no timetable exists at all: the permanent decisions taken earlier never need to be revisited, because the subproblem of the teachers not yet scheduled is independent of them.
-- source:
--   de Werra, An introduction to timetabling, Eur. J. Oper. Res. 19 (1985), p. 155, Proof of Proposition 2.4 ('Let us now show that when decisions x_j and x̄_j have been examined … Hence the problem itself has no timetable.')

import Mathlib
import Definitions.Def_Timetabling85_TwoPeriod_Backtracking

namespace Timetabling85.TwoPeriod

theorem autarky {n : ℕ} (G : SimpleGraph (Fin n × Bool))
    (hpair : ∀ j : Fin n, G.Adj (j, false) (j, true))
    (A : Finset (Fin n × Bool)) (hA : G.IsIndepSet (A : Set (Fin n × Bool)))
    (hclosed : closure G A = A) :
    (∃ T : Finset (Fin n × Bool), G.IsNIndepSet n T) ↔
      ∃ T : Finset (Fin n × Bool), A ⊆ T ∧ G.IsNIndepSet n T := by sorry

end Timetabling85.TwoPeriod
