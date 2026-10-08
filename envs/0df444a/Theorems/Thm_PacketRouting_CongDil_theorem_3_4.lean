-- Prove2me | Theorems.Thm_PacketRouting_CongDil_theorem_3_4
-- name    : PacketRouting.CongDil.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:03:16.018547+00:00
-- url     : https://prove2.me/theorems/30f774c7-1a65-4683-b1f3-567110ee996c
-- title:
--   Theorem 3.4, p. 11 — edge-simple paths with congestion c and dilation d admit a schedule of length O(c + d) with constant-size edge queues
-- statement:
--   Consider store-and-forward routing on a directed network: packets move from their origins to their destinations along prescribed paths, in synchronized time steps, crossing at most one edge per step; a packet that has crossed an edge waits in the edge queue at the head of that edge until it crosses the next edge of its path. The paths are edge-simple, have congestion $c$ (no edge lies on more than $c$ paths) and dilation $d$ (no path has more than $d$ edges).
--
--   **Theorem 3.4.** There are absolute constants $K$ and $Q$ such that for every network, every finite set of packets with edge-simple paths of congestion at most $c$ and dilation at most $d$ admits a schedule
--
--   1. of length at most
--   $$
--   K\,(c+d),
--   $$
--   2. in which at most one packet traverses each edge of the network at each step, and
--   3. in which every edge queue holds at most $Q$ packets at every step.
--
--   In the words of §3 (p. 7), "at most a constant number of packets wait in each queue at each step. Note that there are no restrictions on the size, topology, or degree of the network or on the number of packets." Since every schedule needs at least $\max(c,d)$ steps, the bound is optimal up to the constant factor, and it holds for every network and every choice of paths. By the job-shop reading of §1 (pp. 5–6), it also shows that any job-shop problem with unit-time operations, in which no job visits a machine twice, can be scheduled in $O(c+d)$ steps.
--
--   **Formalization Note** A schedule records the step at which each packet crosses each edge of its path, strictly increasing along the path, starting at step 1; its length is the last crossing step. The queue bound counts only edge queues (initial and final queues are fixed by the instance, p. 2), at the end of each step. $K$ and $Q$ are quantified before the network and the packets, so they are absolute. No finiteness of the network is assumed.
-- source:
--   Leighton, Maggs & Rao, Packet routing and job-shop scheduling in O(congestion + dilation) steps, authors' manuscript (preprint of Combinatorica 14 (1994), DOI 10.1007/BF01215349), p. 11, Theorem 3.4 (restated p. 7, opening of §3)

import Mathlib
import Definitions.Def_PacketRouting_CongDil_Network
import Definitions.Def_PacketRouting_CongDil_Timetable

namespace PacketRouting.CongDil

/-- Theorem 3.4 (Leighton–Maggs–Rao, p. 11): there are absolute constants `K` and `Q` such that
for every directed network, every finite set of packets with edge-simple paths of congestion at
most `c` and dilation at most `d`, there is a schedule of length at most `K (c + d)` in which at
most one packet traverses each edge at each step and every edge queue holds at most `Q` packets
at every step. -/
theorem theorem_3_4 :
    ∃ K Q : ℕ, ∀ (V E P : Type) [Fintype P] (src tgt : E → V) (path : P → List E),
      (∀ p, IsEdgeSimplePath src tgt (path p)) →
      ∀ c d : ℕ, CongestionLE path c → DilationLE path d →
      ∃ τ : Timetable path, τ.Valid ∧ τ.LengthLE (K * (c + d)) ∧
        ∀ (g : E) (t : ℕ), τ.queueSize g t ≤ Q := by sorry

end PacketRouting.CongDil
