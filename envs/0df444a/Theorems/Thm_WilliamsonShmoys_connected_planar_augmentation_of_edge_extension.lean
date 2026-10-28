-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_augmentation_of_edge_extension
-- name    : WilliamsonShmoys.connected_planar_augmentation_of_edge_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T11:21:46.784136+00:00
-- url     : https://prove2.me/theorems/b089e626-2ae2-4433-993f-da8b5105daa5
-- title:
--   Iterate planar component-joining extensions
-- statement:
--   If every disconnected drawable graph on this vertex type can be extended by one planar edge between components, finitely many such extensions yield a connected drawable supergraph with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_augmentation_of_edge_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hInsert : forall (G : SimpleGraph V),
      3 <= Fintype.card V ->
      WilliamsonShmoys.HasPlanarDrawingOn G -> ¬ G.Connected ->
      Exists fun H : SimpleGraph V =>
        (Exists fun u : V => Exists fun v : V =>
          u ≠ v ∧ ¬ G.Reachable u v ∧
          (forall x y : V,
            H.Adj x y ↔ G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u))) ∧
        WilliamsonShmoys.HasPlanarDrawingOn H) :
    Exists fun H : SimpleGraph V =>
      (forall u v : V, K.Adj u v -> H.Adj u v) ∧
      K.edgeSet.ncard <= H.edgeSet.ncard ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
