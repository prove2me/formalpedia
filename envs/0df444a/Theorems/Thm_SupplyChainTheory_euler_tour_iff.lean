-- Prove2me | Theorems.Thm_SupplyChainTheory_euler_tour_iff
-- name    : SupplyChainTheory.euler_tour_iff
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:57:34.363384+00:00
-- url     : https://prove2.me/theorems/bbc2443a-1c5c-4092-8dc9-d8710ea8dfd1
-- title:
--   Theorem 10.10 (Euler): a connected graph has an Eulerian tour iff every node has even degree
-- statement:
--   **Theorem 10.10.** An undirected, connected graph has an Eulerian tour, a closed walk that
--   traverses every edge exactly once, if and only if every node has even degree.
--
--   The book omits the proof. Necessity is the observation that a closed walk enters and leaves
--   each node equally often; sufficiency is Hierholzer's construction, splicing closed trails until
--   all edges are used. This is the fact that turns a doubled spanning tree, or a tree plus a
--   perfect matching on its odd nodes, into a closed walk through all the nodes, which the MST and
--   Christofides heuristics then shortcut.
--
--   **Formalization Note** Stated for Mathlib simple graphs on a finite vertex type; the doubled
--   trees of the heuristics are handled through their walks in the other items.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 431, Sect. 10.4.6, Theorem 10.10: 'Proof. Omitted; see, e.g., Graver and Watkins (1977)'

import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem euler_tour_iff {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) :
    (∀ v, Even (G.degree v)) ↔ ∃ (v : V) (p : G.Walk v v), p.IsEulerian := by sorry

end SupplyChainTheory
