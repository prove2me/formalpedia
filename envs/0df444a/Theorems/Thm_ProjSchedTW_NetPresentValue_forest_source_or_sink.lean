-- Prove2me | Theorems.Thm_ProjSchedTW_NetPresentValue_forest_source_or_sink
-- name    : ProjSchedTW.NetPresentValue.forest_source_or_sink
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T11:07:51.353963+00:00
-- url     : https://prove2.me/theorems/7963f9e6-6362-4c82-adbc-1032f09baecb
-- title:
--   Proposition 3.5.4 — a forest has a source with at most one successor or a sink with exactly one predecessor
-- statement:
--   Let $A$ be the arc set of a directed forest on a finite nonempty node set $V$: there are no loops and no pair of opposite arcs, and the underlying undirected graph has no cycle (so every weakly connected component is a tree). A **source** is a node without predecessors and a **sink** a node without successors. Then there is a node $v$ such that
--   $$v\ \text{is a source with at most one successor}\quad\text{or}\quad v\ \text{is a sink with exactly one predecessor}.$$
--
--   In the book this property of forests (Berge 1976) is what makes the steepest descent direction problem for the net present value objective solvable by repeatedly removing such a node from the spanning forest.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 252, Proposition 3.5.4; definition of tree and forest p. 216

import Mathlib

namespace ProjSchedTW.NetPresentValue

/-- Proposition 3.5.4 (p. 252). A forest (a directed graph each of whose weakly connected
components is a tree, §3.2, p. 216) on a finite nonempty node set `V`, given by its arc set `A`
(no loops, no pair of opposite arcs, underlying undirected graph acyclic), possesses a source (no
predecessor) with at most one successor or a sink (no successor) with exactly one predecessor. -/
theorem forest_source_or_sink {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : Finset (V × V)) (hasymm : ∀ a b : V, (a, b) ∈ A → (b, a) ∉ A)
    (hacyc : (SimpleGraph.fromRel (fun a b => (a, b) ∈ A)).IsAcyclic) :
    ∃ v : V,
      ((∀ u, (u, v) ∉ A) ∧ (A.filter (fun e => e.1 = v)).card ≤ 1) ∨
      ((∀ w, (v, w) ∉ A) ∧ (A.filter (fun e => e.2 = v)).card = 1) := by sorry

end ProjSchedTW.NetPresentValue
