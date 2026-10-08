-- Prove2me | Theorems.Thm_Timetabling85_CourseColoring_coloring_interpretation
-- name    : Timetabling85.CourseColoring.coloring_interpretation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:16.099257+00:00
-- url     : https://prove2.me/theorems/cb6a5382-4106-4351-90ae-ed24b11cbefc
-- title:
--   Proof of Proposition 3.1, p. 158 — lecture l_a of K_b is at period k iff m_ab has the color of period-node k; colorings of Ĝ ↔ feasible schedules
-- statement:
--   Let $P$ be a course scheduling problem with unavailabilities and preassignments (CSUP) in $p$ periods, and let $\hat G$ be its graph: lecture-nodes $m_{ab}$, period-nodes $1,\dots,p$, the edges of the lecture graph, all pairs of period-nodes, $m_{ab}$ joined to $k$ when course $K_b$ cannot be held at period $k$, and $m_{ab}$ joined to every $k \ne \bar k$ when $l_a$ has to be held at period $\bar k$.
--
--   1. For every node colouring $c$ of $\hat G$ with $p$ colours there is a solution $s$ of $P$ in $p$ periods with
--   $$s(l_a \text{ of } K_b) = k \iff c(m_{ab}) = c(k) \qquad \text{for every lecture and every period } k.$$
--   2. Conversely, for every solution $s$ of $P$ in $p$ periods there is a node colouring $c$ of $\hat G$ with $p$ colours related to $s$ in the same way.
--
--   This is the interpretation of the coloured graph $\hat G$ given in the proof of Proposition 3.1: the schedule is read off a colouring through the colours of the period-nodes.
--
--   **Formalization Note** The colouring's palette is `Fin p`, but the statement does not require period-node $k$ to receive colour $k$: a colouring may permute the colours of the period clique, and the schedule is read through the colour of each period-node.
-- source:
--   de Werra, An introduction to timetabling, Eur. J. Oper. Res. 19 (1985), p. 158, proof of Proposition 3.1, "The interpretation of the colored graph Ĝ is the following: …"

import Mathlib
import Definitions.Def_Timetabling85_CourseColoring_CSUP

namespace Timetabling85.CourseColoring

theorem coloring_interpretation {q r p : ℕ} (P : CSUP q r p) :
    (∀ c : P.csupGraph.Coloring (Fin p), ∃ s : P.Lecture → Fin p, P.IsFeasible s ∧
      ∀ (l : P.Lecture) (k : Fin p), s l = k ↔ c (Sum.inl l) = c (Sum.inr k)) ∧
    (∀ s : P.Lecture → Fin p, P.IsFeasible s → ∃ c : P.csupGraph.Coloring (Fin p),
      ∀ (l : P.Lecture) (k : Fin p), s l = k ↔ c (Sum.inl l) = c (Sum.inr k)) := by sorry

end Timetabling85.CourseColoring
