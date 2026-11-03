-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_component_aggregation__p2m_6875723b_f815_435e_a204_8de0d4b60ca9_a3
-- name    : WilliamsonShmoys.disconnected_component_aggregation__p2m_6875723b_f815_435e_a204_8de0d4b60ca9_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:55:28.19387+00:00
-- url     : https://prove2.me/theorems/666f06c4-d624-4127-b254-b308e951621e
-- title:
--   Aggregate component edge bounds for a disconnected graph
-- statement:
--   If every connected component satisfies the bound `3|C|−3` and the finite graph is disconnected, then the whole graph satisfies `3|V|−6`. Partition vertices and edges by component, sum the component inequalities, and use that disconnectedness gives at least two components. This removes the finite counting and aggregation work from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_component_aggregation__p2m_6875723b_f815_435e_a204_8de0d4b60ca9_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdisconn : ¬ K.Connected)
    (hcomponents : ∀ c : K.ConnectedComponent,
      letI : Fintype {v : V // v ∈ c.supp} := Fintype.ofFinite _
      letI : DecidableRel ((K.induce c.supp).Adj) := Classical.decRel _
      (K.induce c.supp).edgeFinset.card ≤
        3 * Fintype.card {v : V // v ∈ c.supp} - 3) :
    letI : (L : SimpleGraph V) → DecidableRel L.Adj :=
      fun L => Classical.decRel L.Adj
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
