-- Prove2me | Theorems.Thm_WilliamsonShmoys_connect_drawn_components
-- name    : WilliamsonShmoys.connect_drawn_components
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T12:12:54.095693+00:00
-- url     : https://prove2.me/theorems/6087d785-1502-4951-be5d-3cd62c7daaaa
-- title:
--   Connect components while preserving a planar drawing
-- statement:
--   Any drawable graph on a finite ordered vertex type with at least three vertices is contained in a connected drawable graph on the same vertices. Add edges between distinct embedded components through the complement of the drawing, repeating until connected; each added arc must avoid the existing drawing except at its endpoints.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connect_drawn_components
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.Connected := by sorry
