-- Prove2me | Theorems.Thm_PacketRouting_CongDil_final_simulation
-- name    : PacketRouting.CongDil.final_simulation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:03:33.25268+00:00
-- url     : https://prove2.me/theorems/0bf075c0-2239-4637-9eda-2036c9be4d72
-- title:
--   §3.2, pp. 12–13 — a schedule with constant relative congestion in constant-size frames and rare waits becomes a valid schedule with constant queues
-- statement:
--   This is the last step of the proof of Theorem 3.4: the schedule $S_j$ produced by the refinements "almost" routes the packets, and a constant slow-down finishes the job.
--
--   Fix constants $r\in\mathbb R$, $k_0\in\mathbb N$ and $k_1\ge 2$. **Claim (pp. 12–13).** There are constants $K$ and $Q$ such that the following holds for every directed network and every finite set of packets with edge-simple paths. Let $S$ be a schedule of length at most $L$ such that
--
--   1. the relative congestion is at most $r$ in every frame of size $k_0$ or greater: at most $rT$ packets cross any edge in any $T$ consecutive steps, for all $T\ge\max(1,k_0)$;
--   2. every packet waits (in an edge queue) at most once in any $k_1$ consecutive steps.
--
--   Then there is a schedule of the same packets along the same paths with
--   $$
--   \text{length}\le K\,L,
--   $$
--   in which at most one packet traverses each edge at each step, and in which every edge queue holds at most $Q$ packets at every step.
--
--   **Formalization Note** The constants $K,Q$ are chosen after $r,k_0,k_1$ and before the network and the schedule. The page's "factor of 2 increase in the queue size" describes its construction and is not part of the claim. The hypothesis $k_1\ge2$ makes the waiting condition non-empty: for $k_1=1$ it holds for every schedule.
-- source:
--   Leighton, Maggs & Rao, Packet routing and job-shop scheduling in O(congestion + dilation) steps, authors' manuscript (preprint of Combinatorica 14 (1994), DOI 10.1007/BF01215349), pp. 12–13, proof of Theorem 3.4, construction of the final schedule from S_j (unnumbered)

import Mathlib
import Definitions.Def_PacketRouting_CongDil_Network
import Definitions.Def_PacketRouting_CongDil_Timetable

namespace PacketRouting.CongDil

/-- The final step of the proof of Theorem 3.4 (Leighton–Maggs–Rao, §3.2, pp. 12–13): for all
constants `r`, `k₀` and `k₁ ≥ 2` there are constants `K` and `Q` such that every schedule `S`
of a set of packets with edge-simple paths, of length at most `L`, with relative congestion at
most `r` in every frame of size `k₀` or greater, and in which every packet waits at most once
every `k₁` steps, can be turned into a schedule of the same packets along the same paths of
length at most `K L` in which at most one packet traverses each edge at each step and every edge
queue holds at most `Q` packets. -/
theorem final_simulation :
    ∀ (r : ℝ) (k₀ k₁ : ℕ), 2 ≤ k₁ → ∃ K Q : ℕ,
      ∀ (V E P : Type) [Fintype P] (src tgt : E → V) (path : P → List E),
      (∀ p, IsEdgeSimplePath src tgt (path p)) →
      ∀ (S : Timetable path) (L : ℕ), S.LengthLE L → S.RelCongLE r k₀ →
        S.WaitsAtMostOnceEvery k₁ →
      ∃ τ : Timetable path, τ.Valid ∧ τ.LengthLE (K * L) ∧
        ∀ (g : E) (t : ℕ), τ.queueSize g t ≤ Q := by sorry

end PacketRouting.CongDil
