-- Prove2me | Theorems.Thm_Timetabling85_TwoPeriod_closure_subset_of_stable
-- name    : Timetabling85.TwoPeriod.closure_subset_of_stable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:01.061947+00:00
-- url     : https://prove2.me/theorems/b9763ba4-57fa-4ea7-9d9f-bb62760b1199
-- title:
--   Proof of Proposition 2.4, p. 155 — implications of chosen schedules stay inside every timetable that contains them
-- statement:
--   Let $G$ be a graph on the nodes $x_j=(j,\mathrm{true})$, $\bar x_j=(j,\mathrm{false})$ of $n$ teachers in which $x_j$ and $\bar x_j$ are linked for every $j$. Let $T$ be a set of $n$ pairwise non-adjacent nodes of $G$ (a timetable), and let $S\subseteq T$. Then
--   $$
--   \mathrm{cl}(S)\subseteq T,
--   $$
--   where $\mathrm{cl}(S)$ is the set of all implications of the choices $S$.
--
--   Consequently, if the implications of a set of choices are not pairwise non-adjacent ("for some teacher no schedule can be found"), then no timetable contains those choices. This is what justifies reversing a decision in the limited backtracking.
-- source:
--   de Werra, An introduction to timetabling, Eur. J. Oper. Res. 19 (1985), p. 155, Proof of Proposition 2.4 ('one considers all the implications of this choice')

import Mathlib
import Definitions.Def_Timetabling85_TwoPeriod_Backtracking

namespace Timetabling85.TwoPeriod

theorem closure_subset_of_stable {n : ℕ} (G : SimpleGraph (Fin n × Bool))
    (hpair : ∀ j : Fin n, G.Adj (j, false) (j, true))
    (T : Finset (Fin n × Bool)) (hT : G.IsNIndepSet n T)
    (S : Finset (Fin n × Bool)) (hS : S ⊆ T) :
    closure G S ⊆ T := by sorry

end Timetabling85.TwoPeriod
