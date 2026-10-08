-- Prove2me | Theorems.Thm_Timetabling85_TwoPeriod_limited_backtracking_correct
-- name    : Timetabling85.TwoPeriod.limited_backtracking_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:58.285167+00:00
-- url     : https://prove2.me/theorems/c00aa90b-82e0-4e6d-9eee-430404055bfd
-- title:
--   Proposition 2.4 and Remark, pp. 154–155 — limited backtracking terminates, and its success and failure answers are correct
-- statement:
--   Let $G$ be a graph on the nodes $x_j=(j,\mathrm{true})$, $\bar x_j=(j,\mathrm{false})$ of $n$ teachers in which $x_j$ and $\bar x_j$ are linked for every $j$ (each teacher has two possible schedules, and they are incompatible). Run de Werra's limited backtracking from $\mathrm{run}(\emptyset)$, with arbitrary choices of the teacher to decide and of the first schedule tried. Then:
--   1. **termination** — there is no infinite run: the move relation is well founded from $\mathrm{run}(\emptyset)$;
--   2. **progress** — every reachable state $\mathrm{run}(A)$ in which some teacher is not yet fixed has a move;
--   3. **success is correct** — if $\mathrm{run}(A)$ is reachable and every teacher is fixed in $A$, then $A$ is a set of $n$ pairwise non-adjacent nodes of $G$, i.e. a timetable;
--   4. **failure is correct** — if $\mathrm{fail}$ is reachable, then
--   $$
--   G \text{ has no set of } n \text{ pairwise non-adjacent nodes.}
--   $$
--
--   Together, every run of the procedure stops after finitely many decisions and returns a timetable exactly when one exists. Combined with the reduction of CT4 to the conflict graph, this is the correctness content of de Werra's Proposition 2.4 (the case of CT4 in which every teacher is available during at most 2 periods) and of the Remark that follows it.
--
--   **Formalization Note** The $O(n^2)$ running-time claim of Proposition 2.4 and of the Remark is not formalized: the page fixes no machine model and no constant. Termination (clause 1) is the formal content; each move fixes at least one more teacher. All four clauses quantify over every run of the nondeterministic move relation, not over one fixed choice rule; clauses 1 and 2 rule out a procedure that never moves.
-- source:
--   de Werra, An introduction to timetabling, Eur. J. Oper. Res. 19 (1985), pp. 154–155, Proposition 2.4 and its proof; Remark, p. 155

import Mathlib
import Definitions.Def_Timetabling85_TwoPeriod_Backtracking

namespace Timetabling85.TwoPeriod

theorem limited_backtracking_correct {n : ℕ} (G : SimpleGraph (Fin n × Bool))
    (hpair : ∀ j : Fin n, G.Adj (j, false) (j, true)) :
    Acc (fun t s => Step G s t) (State.run ∅) ∧
    (∀ A : Finset (Fin n × Bool), Reachable G (State.run A) → (∃ j, ¬ Fixed A j) →
      ∃ t, Step G (State.run A) t) ∧
    (∀ A : Finset (Fin n × Bool), Reachable G (State.run A) → (∀ j, Fixed A j) →
      G.IsNIndepSet n A) ∧
    (Reachable G State.fail → ¬ ∃ T : Finset (Fin n × Bool), G.IsNIndepSet n T) := by sorry

end Timetabling85.TwoPeriod
