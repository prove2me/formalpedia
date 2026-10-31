-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_edge_augmentation
-- name    : WilliamsonShmoys.drawable_graph_edge_augmentation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:14:20.674865+00:00
-- url     : https://prove2.me/theorems/b1d5eb3b-0579-47bb-a5d6-42c62faa74a4
-- title:
--   Augmenting a drawable graph below the planar edge bound
-- statement:
--   If a drawable simple graph on at least three vertices has fewer than 3|V|−6 edges, one can add an edge while preserving drawability on the same vertex set. A proof can extend the drawing to a maximal planar graph, joining components through the unbounded face and adding a diagonal in any nontriangular face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_edge_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hV : 3 ≤ Fintype.card V)
    (hsmall : X.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ Y : SimpleGraph V, X < Y ∧ WilliamsonShmoys.HasPlanarDrawingOn Y := by sorry
