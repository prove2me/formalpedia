-- Prove2me | Theorems.Thm_Timetabling85_TwoPeriod_remark_perfect_matching
-- name    : Timetabling85.TwoPeriod.remark_perfect_matching
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:43.255708+00:00
-- url     : https://prove2.me/theorems/ad14d2e3-24e4-4315-865e-1e397f76c9dd
-- title:
--   Remark, p. 155 — in a graph with a perfect matching a stable set has at most |X|/2 nodes, one end of each matching edge
-- statement:
--   Let $G=(X,E)$ be a finite graph with a perfect matching $M$. Then
--   1. every stable set $S$ of $G$ satisfies $|S|\le |X|/2$;
--   2. every stable set $S$ with $|S|=|X|/2$ contains exactly one endpoint of every edge of $M$: for each edge $vw\in M$,
--   $$
--   v\in S \iff w\notin S .
--   $$
--
--   These two facts are what make de Werra's Remark work: identifying the edges of $M$ with the pairs $\{x_j,\bar x_j\}$ of the proof of Proposition 2.4, a stable set of $|X|/2$ nodes is exactly a choice of one node per pair with no conflicts, so the limited backtracking decides whether such a set exists.
--
--   **Formalization Note** The Remark's algorithmic claim (an $O(n^2)$ algorithm) is not formalized; the statement records the combinatorial content that transports the procedure from graphs on $\mathrm{Fin}\,n\times\mathrm{Bool}$ to any graph with a perfect matching. $|X|/2$ is natural-number division, exact here because a perfect matching makes $|X|$ even.
-- source:
--   de Werra, An introduction to timetabling, Eur. J. Oper. Res. 19 (1985), p. 155, Remark after the proof of Proposition 2.4

import Mathlib

namespace Timetabling85.TwoPeriod

theorem remark_perfect_matching {X : Type*} [Fintype X] [DecidableEq X]
    (G : SimpleGraph X) (M : G.Subgraph) (hM : M.IsPerfectMatching) :
    (∀ S : Finset X, G.IsIndepSet (S : Set X) → S.card ≤ Fintype.card X / 2) ∧
    (∀ S : Finset X, G.IsIndepSet (S : Set X) → S.card = Fintype.card X / 2 →
      ∀ v w : X, M.Adj v w → (v ∈ S ↔ w ∉ S)) := by sorry

end Timetabling85.TwoPeriod
