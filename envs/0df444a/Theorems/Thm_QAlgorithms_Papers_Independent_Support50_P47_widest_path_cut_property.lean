-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P47_widest_path_cut_property
-- name    : QAlgorithms.Papers.Independent.Support50.P47.widest_path_cut_property
-- status  : Open
-- author  : @Goku
-- created : 2026-10-24T00:00:10.924933+00:00
-- url     : https://prove2.me/theorems/4ff615fd-fd51-4d72-a810-2cad78824b9d
-- title:
--   Widest path: equality with the minimum maximum-edge cut
-- statement:
--   Let $G=(V,E)$ be a finite connected undirected graph with distinct vertices $a,b$, and let $W:E\to\mathbb R$ assign an arbitrary real weight to every edge. Parallel edges, if present, retain distinct labels. Let $\Omega_{ab}$ contain all simple paths from $a$ to $b$. For a vertex set $A$ containing $a$ but not $b$, let $\delta(A)$ be the set of edges with exactly one endpoint in $A$. Define a path's weight as its minimum edge weight and a cut's weight as its maximum crossing-edge weight. Then
--
--   $$
--   \max_{p\in\Omega_{ab}}\min_{e\in p} W(e)
--   =\min_{A:\,a\in A,\ b\notin A}\max_{e\in\delta(A)}W(e).
--   $$
--
--   Both extrema are attained. Every path and separating cut has a nonempty finite edge set. Negative weights are allowed. This identifies the bottleneck routing value with a cut obstruction, without quantum-channel assumptions.
--
--   **Formalization Note** The Lean conclusion supplies an optimizing path and cut, equality of their weights, and the universal optimality inequalities. Edge orientation in the data only chooses endpoint names; traversals and cut membership are undirected.
-- source:
--   Capacities of repeater-assisted quantum communications, arXiv:1601.00966v4, PDF p. 24, Proposition 12, Eq.(131)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P47

namespace QAlgorithms.Papers.Independent.Support50.P47

noncomputable section

universe u v

/-- PDF pp.23–24, Proposition 12, Eq.(131): the widest simple endpoint route
and a minimum endpoint cut exist and have the same weight. Weights are arbitrary
reals, including negative ones; parallel labelled edges are retained.
The universal clauses state both extrema with attainment, avoiding totalized
suprema over empty or unbounded collections. No quantum hypothesis is imposed. -/
theorem widest_path_cut_property {V : Type u} {E : Type v}
    [Fintype V] [Fintype E] (G : WeightedNetwork V E)
    (hconn : IsConnected G) (a b : V) (hab : a ≠ b) :
    ∃ p : Route G a b, ∃ A : Set V,
      a ∈ A ∧ b ∉ A ∧ routeWeight G p = cutWeight G A ∧
      (∀ q : Route G a b, routeWeight G q ≤ routeWeight G p) ∧
      (∀ B : Set V, a ∈ B → b ∉ B → cutWeight G A ≤ cutWeight G B) := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P47
