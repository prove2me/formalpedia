-- Prove2me | Theorems.Thm_RunwayCPS_Makespan_lemma_2
-- name    : RunwayCPS.Makespan.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:40.845333+00:00
-- url     : https://prove2.me/theorems/f021f990-fa61-497a-9736-ada4fc91ea1f
-- title:
--   Lemma 2 — in the position-constrained network, a path that puts a before b has a node with a before b (Case II)
-- statement:
--   Let $a<b$ be two aircraft (FCFS labels) and suppose a precedence constraint requires $b$ to land before $a$ (Case II). The **position-constrained network** is the CPS network with maximum shift $k$ from which every node is removed that has $a$ at a position less than $b-k$ or $b$ at a position greater than $a+k$. Let $v_1,\dots,v_n$ be a source-sink path of the position-constrained network, and let $f$ denote positions in its sequence.
--
--   If $f(a)<f(b)$, then
--
--   $$\text{some node } v_s,\ 1\le s\le n,\ \text{contains } a \text{ before } b.$$
--
--   So, after the position filter, deleting the nodes in which $a$ appears before $b$ removes every source-sink path that violates the constraint.
--
--   **Formalization Note** Aircraft and positions are 0-based, stages 1-based. The removal rule is the paper's printed one ($a$ at a position $<b-k$, $b$ at a position $>a+k$); the constraints stated just before it in the paper ($\ge b-k+1$, $\le a+k-1$) would remove more nodes and give a weaker lemma.
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), p. 1654, §3.1, Case II, position-constrained network, Lemma 2

import Mathlib
import Definitions.Def_RunwayCPS_Makespan_Network

namespace RunwayCPS.Makespan

/-- Lemma 2 (p. 1654), Case II: for aircraft `a < b` (FCFS labels) with the precedence
requirement that `b` lands before `a`, consider the position-constrained network, i.e. the CPS
network without the nodes having `a` at a position less than `b - k` or `b` at a position
greater than `a + k`. If a source-sink path of this network places `a` before `b` in its
sequence, then some node of the path contains `a` before `b`. -/
theorem lemma_2 {n : ℕ} [NeZero n] (k : ℕ) (a b : Fin n) (hab : a < b)
    (v : ℕ → List (Fin n))
    (hv : IsPathIn n (fun p w => IsStageNode k p w ∧ ¬ PosViolates k p b a w) k v)
    (hord : ∃ p q : Fin n, p < q ∧ pathSeq v p = a ∧ pathSeq v q = b) :
    ∃ s, 1 ≤ s ∧ s ≤ n ∧ BeforeIn (v s) a b := by sorry

end RunwayCPS.Makespan
