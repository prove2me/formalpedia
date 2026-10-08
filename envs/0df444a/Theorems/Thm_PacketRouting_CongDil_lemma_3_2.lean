-- Prove2me | Theorems.Thm_PacketRouting_CongDil_lemma_3_2
-- name    : PacketRouting.CongDil.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:03:04.765485+00:00
-- url     : https://prove2.me/theorems/61c73495-4d4c-4feb-912a-5bccd50769cb
-- title:
--   Lemma 3.2, p. 8 — a no-edge-wait schedule of length O(d) with relative congestion ≤ 1 in every frame of size ≥ log d (c = d)
-- statement:
--   Consider a directed network and a finite set of packets with edge-simple paths whose congestion and dilation are both at most $d$ (the normalization $c=d$ with which the proof of Lemma 3.2 begins on p. 9).
--
--   **Lemma 3.2.** There is an absolute constant $K$ such that for every such instance there is a schedule $S_1$ with:
--
--   1. length at most $K d$;
--   2. no waiting in edge queues: once a packet starts moving it crosses one edge of its path at every step until it reaches its destination;
--   3. relative congestion at most $1$ in every frame of size $\log_2 d$ or greater: for every edge $g$, every start $t$ and every frame size $T\ge 1$ with $T\ge \log_2 d$,
--   $$
--   \#\{p : p \text{ crosses } g \text{ at a step of } [t,t+T)\}\;\le\;T .
--   $$
--
--   The schedule need not be valid: several packets may cross the same edge at the same step. $S_1$ is the starting point of the recursive refinement that proves Theorem 3.4.
--
--   **Formalization Note** The page states the lemma for congestion $c$ and dilation $d$ with length $O(c+d)$ and frames of size $\log d$; its proof assumes $c=d$ without loss of generality, and the frame-size bound it establishes is $\log$ of that common value. The statement is therefore made for a common bound $d$ on congestion and dilation; the general case follows by taking $d:=\max(c,d)$. Frames have size at least $1$ in addition to $\log_2 d$, since $\log_2 d\le 0$ for $d\le1$.
-- source:
--   Leighton, Maggs & Rao, Packet routing and job-shop scheduling in O(congestion + dilation) steps, authors' manuscript (preprint of Combinatorica 14 (1994), DOI 10.1007/BF01215349), p. 8, Lemma 3.2 (normalization c = d from its proof, p. 9)

import Mathlib
import Definitions.Def_PacketRouting_CongDil_Network
import Definitions.Def_PacketRouting_CongDil_Timetable

namespace PacketRouting.CongDil

/-- Lemma 3.2 (Leighton–Maggs–Rao, p. 8), in the normalization `c = d` of its proof (p. 9):
there is an absolute constant `K` such that for every set of packets with edge-simple paths of
congestion at most `d` and dilation at most `d` there is a schedule of length at most `K d` in
which packets never wait in edge queues and in which, in every frame of size `T ≥ log₂ d`
(and `T ≥ 1`), at most `T` packets use any edge. -/
theorem lemma_3_2 :
    ∃ K : ℕ, ∀ (V E P : Type) [Fintype P] (src tgt : E → V) (path : P → List E),
      (∀ p, IsEdgeSimplePath src tgt (path p)) →
      ∀ d : ℕ, CongestionLE path d → DilationLE path d →
      ∃ τ : Timetable path, τ.NoEdgeWait ∧ τ.LengthLE (K * d) ∧
        τ.RelCongLE 1 (Real.logb 2 d) := by sorry

end PacketRouting.CongDil
