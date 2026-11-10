-- Prove2me | Theorems.Thm_SmallClassesNeighbourhood_Linear_bounded_degree_spanning_tree
-- name    : SmallClassesNeighbourhood.Linear.bounded_degree_spanning_tree
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:35:08.851203+00:00
-- url     : https://prove2.me/theorems/0f0cf930-3a7a-404a-a347-85ef2dbcfccc
-- title:
--   Lemma 15 — induced subgraph with a bounded-degree spanning tree
-- statement:
--   Let G be a finite nonempty graph of minimum degree at least the nonnegative integer d. There is a nonempty vertex set S for which H=G[S] has minimum degree at least d, and a spanning tree T of H such that
--
--   $$\delta(H)\ge d,\qquad T\subseteq H,\qquad \Delta(T)\le d.$$
--
--   The tree and H have the same actual vertices. G need not be connected or bipartite. The cases d=0 and d=1 are included. This supplies the auxiliary tree in the few-defects case.
--
--   Differences from the source:
--   - encoding: a graph of minimum degree at least d → a finite nonempty graph, with every vertex degree at least d; reason: minimum degree here presupposes a nonempty graph; all degrees are finite, and d is a nonnegative integer
-- source:
--   John Sylvester, Viktor Zamaraev, Maksim Zhukovskii, STOC 2027 submission #1126 (October 2026), Lemma 15, printed p. 11 (PDF p. 12)

import Definitions.Def_SmallClassesNeighbourhood_Linear_graphBasics

namespace SmallClassesNeighbourhood.Linear

theorem bounded_degree_spanning_tree {V : Type} [Fintype V] [DecidableEq V]
    [Nonempty V] (G : SimpleGraph V) (d : ℕ)
    (hdegree : ∀ v : V, d ≤ Nat.card (G.neighborSet v)) :
    ∃ S : Finset V, S.Nonempty ∧
      (∀ v : (↑S : Set V), d ≤ Nat.card ((G.induce (↑S : Set V)).neighborSet v)) ∧
      ∃ T : SimpleGraph (↑S : Set V), T ≤ G.induce (↑S : Set V) ∧ T.IsTree ∧
        ∀ v, Nat.card (T.neighborSet v) ≤ d := by sorry

end SmallClassesNeighbourhood.Linear
