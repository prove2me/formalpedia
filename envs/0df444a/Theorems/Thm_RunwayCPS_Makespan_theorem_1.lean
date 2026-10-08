-- Prove2me | Theorems.Thm_RunwayCPS_Makespan_theorem_1
-- name    : RunwayCPS.Makespan.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:53.424857+00:00
-- url     : https://prove2.me/theorems/71a2536d-ba34-468a-9c76-8ff338a8f612
-- title:
--   Theorem 1 — k-CPS sequences are exactly the sequences of source-sink paths of the CPS network
-- statement:
--   Let $n\ge1$ aircraft be labelled in FCFS order and let $k\ge0$ be the maximum position shift. Consider the CPS network: its stage-$p$ nodes are the lists of $\min\{2k+1,p\}$ distinct aircraft that may occupy positions $p-\min\{2k+1,p\}+1,\dots,p$, and arcs join nodes of consecutive stages whose subsequences overlap in $\min\{2k,p\}$ aircraft. A source-sink path $v_1,\dots,v_n$ **corresponds** to the sequence that places at position $p$ the final aircraft of $v_p$.
--
--   For every map $\sigma$ from positions to aircraft,
--
--   $$\sigma \text{ is a } k\text{-CPS sequence}\iff \sigma \text{ is the sequence of some source-sink path of the CPS network.}$$
--
--   In particular, the sequence of every source-sink path is a permutation in which every aircraft is within $k$ positions of its FCFS position, and every such permutation arises from a path. This is the result that lets the paper replace the search over permutations by a search over paths of a network with polynomially many nodes for fixed $k$.
--
--   **Formalization Note** Aircraft and positions are 0-based, stages 1-based. The correspondence between sequence and path is stated explicitly, so the statement is not the trivial "some $k$-CPS sequence exists iff some path exists". The network is the unpruned one (no precedence pairs).
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), pp. 1652–1653, Theorem 1 (correspondence as defined in its proof)

import Mathlib
import Definitions.Def_RunwayCPS_Makespan_Network

namespace RunwayCPS.Makespan

/-- Theorem 1 (p. 1652): a sequence `σ` (position ↦ aircraft) is a `k`-CPS sequence if and only
if it is the sequence read off some source-sink path of the (unpruned) CPS network, position `p`
receiving the final aircraft of the path's stage-`p` node. -/
theorem theorem_1 {n : ℕ} [NeZero n] (k : ℕ) (σ : Fin n → Fin n) :
    IsCPS k σ ↔ ∃ v : ℕ → List (Fin n), IsPathIn n (IsStageNode k) k v ∧ pathSeq v = σ := by sorry

end RunwayCPS.Makespan
