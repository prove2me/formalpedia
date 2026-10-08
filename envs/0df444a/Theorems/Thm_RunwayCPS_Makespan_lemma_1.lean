-- Prove2me | Theorems.Thm_RunwayCPS_Makespan_lemma_1
-- name    : RunwayCPS.Makespan.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:36.684249+00:00
-- url     : https://prove2.me/theorems/3e6a3e4f-21e2-41fc-ae82-520a1d576aed
-- title:
--   Lemma 1 — a path that puts b before a has a node with b before a (Case I)
-- statement:
--   Let $a<b$ be two aircraft (FCFS labels) and suppose a precedence constraint requires $a$ to land before $b$ (Case I). Let $v_1,\dots,v_n$ be a source-sink path of the CPS network with maximum shift $k$, and let $f$ denote positions in its sequence.
--
--   If $f(a)>f(b)$, then
--
--   $$\text{some node } v_s,\ 1\le s\le n,\ \text{contains } b \text{ before } a.$$
--
--   Consequently, deleting every node in which $b$ appears before $a$ removes every source-sink path that violates the constraint.
--
--   **Formalization Note** Aircraft and positions are 0-based, stages 1-based. "$b$ before $a$ in a node" means that $b$ occurs at a smaller list index than $a$.
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), p. 1653, §3.1, Case I, Lemma 1

import Mathlib
import Definitions.Def_RunwayCPS_Makespan_Network

namespace RunwayCPS.Makespan

/-- Lemma 1 (p. 1653), Case I: for aircraft `a < b` (FCFS labels), if a source-sink path of the
CPS network places `a` after `b` in its sequence, then some node of the path contains `b`
before `a`. -/
theorem lemma_1 {n : ℕ} [NeZero n] (k : ℕ) (a b : Fin n) (hab : a < b)
    (v : ℕ → List (Fin n)) (hv : IsPathIn n (IsStageNode k) k v)
    (hord : ∃ p q : Fin n, q < p ∧ pathSeq v p = a ∧ pathSeq v q = b) :
    ∃ s, 1 ≤ s ∧ s ≤ n ∧ BeforeIn (v s) b a := by sorry

end RunwayCPS.Makespan
