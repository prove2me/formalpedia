-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_add_edge_of_nonreachable
-- name    : WilliamsonShmoys.drawable_add_edge_of_nonreachable
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T15:42:29.684794+00:00
-- url     : https://prove2.me/theorems/1c2becfd-4860-49ee-a6e1-c2849bb57d3a
-- title:
--   A drawable graph can be augmented across components
-- statement:
--   Given a drawable graph and a nonreachable pair of vertices, there is a strict drawable supergraph on the same vertices. The proof rearranges the drawing components and adds an arc joining the pair.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_add_edge_of_nonreachable
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn H) {u v : V}
    (huv : ¬ H.Reachable u v) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧ K ≠ H := by sorry
