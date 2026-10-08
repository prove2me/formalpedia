-- Prove2me | Theorems.Thm_Timetabling85_CourseColoring_prop_3_1
-- name    : Timetabling85.CourseColoring.prop_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:10.441841+00:00
-- url     : https://prove2.me/theorems/0cdec832-91a1-4373-a2f3-c3b9fee87781
-- title:
--   Proposition 3.1, p. 157 — a CSUP has a solution in p periods iff its graph Ĝ has a node coloring with p colors
-- statement:
--   Let $P$ be a course scheduling problem with unavailabilities and preassignments (CSUP) in $p$ periods: courses $K_b$ with their lectures, students each taking a set of courses, for each course a set of periods at which it cannot take place, and for some lectures a period at which they must take place. Let $\hat G$ be the graph constructed in the proof of the proposition: one lecture-node $m_{ab}$ per lecture $l_a$ of course $K_b$ and one period-node per period; two lecture-nodes of one course adjacent; lecture-nodes of distinct courses taken together by some student adjacent; all pairs of period-nodes adjacent; $m_{ab}$ adjacent to period-node $k$ if $K_b$ cannot be scheduled at period $k$; and $m_{ab}$ adjacent to every period-node $k \ne \bar k$ if $l_a$ has to be scheduled at period $\bar k$. Then
--
--   $$P \text{ has a solution in } p \text{ periods} \iff \hat G \text{ has a node coloring with } p \text{ colors}.$$
--
--   The proposition reduces course scheduling with unavailability and preassignment constraints to plain node colouring, so that any node colouring method applies to the constrained problem.
--
--   **Formalization Note** The paper states the proposition as "one can construct a graph $\hat G$ such that …". Read literally as an existential over graphs it would be trivially true (take a complete graph on $p+1$ nodes or an edgeless graph according to the answer), so the statement is made about the specific graph $\hat G$ of the proof, `csupGraph P`, defined in the definitions file. Periods are `Fin p`; $p = 0$ is allowed, and then both sides hold exactly when there are no lectures.
-- source:
--   de Werra, An introduction to timetabling, Eur. J. Oper. Res. 19 (1985), p. 157, Proposition 3.1, with the graph Ĝ of its proof, pp. 157–158

import Mathlib
import Definitions.Def_Timetabling85_CourseColoring_CSUP

namespace Timetabling85.CourseColoring

theorem prop_3_1 {q r p : ℕ} (P : CSUP q r p) :
    (∃ s : P.Lecture → Fin p, P.IsFeasible s) ↔ P.csupGraph.Colorable p := by sorry

end Timetabling85.CourseColoring
