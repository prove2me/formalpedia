-- Prove2me | Theorems.Thm_Timetabling85_CourseColoring_schedule_iff_coloring
-- name    : Timetabling85.CourseColoring.schedule_iff_coloring
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:12.965336+00:00
-- url     : https://prove2.me/theorems/63ea3078-774f-4926-892b-c635609e5ad8
-- title:
--   §3.1, p. 157 — a feasible course schedule in p periods is exactly a node coloring of the lecture graph with p colors
-- statement:
--   Let a course scheduling instance be given: courses $K_b$ with their lectures $l_a$, and students each taking a set of courses. Let $G$ be its lecture graph: one node $m_{ab}$ per lecture, two lecture-nodes of the same course adjacent, and two lecture-nodes of distinct courses $K_b$, $K_{\bar b}$ adjacent whenever some student takes both courses. Let $p \ge 0$.
--
--   Then an assignment $s$ of periods $\{1,\dots,p\}$ to lectures is a feasible course schedule (no two lectures of a course at one period, and no student required to take two lectures at one period) if and only if $s$ is a node colouring of $G$ with $p$ colours:
--   $$s \text{ feasible} \iff s(m) \ne s(m') \text{ for every edge } mm' \text{ of } G.$$
--   In particular
--   $$\exists\, \text{feasible schedule in } p \text{ periods} \iff \chi(G) \le p .$$
--
--   This is the basic graph model of course scheduling, on which the treatment of unavailabilities and preassignments (Proposition 3.1) builds.
--
--   **Formalization Note** The schedule and the colouring are the same function `Lecture → Fin p`; the first conjunct says that the feasible schedules are exactly the underlying functions of the proper colourings of `lectureGraph`, the second is the existence form with `SimpleGraph.Colorable`.
-- source:
--   de Werra, An introduction to timetabling, Eur. J. Oper. Res. 19 (1985), p. 157, §3.1, sentence "A feasible course schedule in p periods will correspond to a node coloring of the above graph with p colors"

import Mathlib
import Definitions.Def_Timetabling85_CourseColoring_CSUP

namespace Timetabling85.CourseColoring

theorem schedule_iff_coloring {q r : ℕ} (I : CourseInstance q r) (p : ℕ) :
    (∀ s : I.Lecture → Fin p,
      I.IsFeasibleSchedule p s ↔ ∃ c : I.lectureGraph.Coloring (Fin p), ⇑c = s) ∧
    ((∃ s : I.Lecture → Fin p, I.IsFeasibleSchedule p s) ↔ I.lectureGraph.Colorable p) := by sorry

end Timetabling85.CourseColoring
