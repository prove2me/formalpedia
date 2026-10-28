-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_induced_connected_and_planar_drawing_for_component_edge_bound
-- name    : WilliamsonShmoys.component_induced_connected_and_planar_drawing_for_component_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:56:20.086191+00:00
-- url     : https://prove2.me/theorems/a1da7969-a570-4f6d-8177-8ace62df86b7
-- title:
--   Connectedness and drawing restriction for an induced component
-- statement:
--   The graph induced by a connected component is connected and inherits a planar drawing from the original graph. This includes singleton components; the parent applies the edge estimate only when the component has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.component_induced_connected_and_planar_drawing_for_component_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (c : M.ConnectedComponent)
    [Fintype {v : V // M.connectedComponentMk v = c}] :
    let S : Type := {v : V // M.connectedComponentMk v = c}
    let H : SimpleGraph S := M.induce (fun v => M.connectedComponentMk v = c)
    H.Connected ∧ HasPlanarDrawingOn H := by sorry
