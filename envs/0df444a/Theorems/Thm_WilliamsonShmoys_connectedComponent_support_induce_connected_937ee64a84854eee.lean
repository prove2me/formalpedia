-- Prove2me | Theorems.Thm_WilliamsonShmoys_connectedComponent_support_induce_connected_937ee64a84854eee
-- name    : WilliamsonShmoys.connectedComponent_support_induce_connected_937ee64a84854eee
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:33:21.312564+00:00
-- url     : https://prove2.me/theorems/5244a397-2a35-486b-8d0f-4fa885dfd380
-- title:
--   A component support induces a connected graph
-- statement:
--   The graph induced on a connected-component support is connected. Lift the reachability path between two support vertices to the subtype graph; every vertex on the path remains in the same component support.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.connectedComponent_support_induce_connected_937ee64a84854eee
    {V : Type} [Fintype V]
    (L : SimpleGraph V)
    (C : L.ConnectedComponent)
    [Fintype (↑C.supp)] :
    (L.induce C.supp).Connected := by sorry
