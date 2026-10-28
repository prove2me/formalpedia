-- Prove2me | Theorems.Thm_WilliamsonShmoys_connectedComponent_support_induce_connected_4db24ad1
-- name    : WilliamsonShmoys.connectedComponent_support_induce_connected_4db24ad1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:10:48.274511+00:00
-- url     : https://prove2.me/theorems/8423ab6b-2db9-41ab-80d0-91c94954b873
-- title:
--   A component support induces a connected graph
-- statement:
--   The graph induced on a component support is connected. Lift paths between support vertices to paths in the induced subtype graph, using the component reachability characterization. The explicit finite-type instance supports formation of the induced graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.connectedComponent_support_induce_connected_4db24ad1
    {V : Type} [Fintype V]
    (L : SimpleGraph V)
    (C : L.ConnectedComponent)
    [Fintype (↥C.supp)] :
    (L.induce C.supp).Connected := by sorry
