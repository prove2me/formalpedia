-- Prove2me | Theorems.Thm_WilliamsonShmoys_connectedPlanarDrawing_edgeUpper
-- name    : WilliamsonShmoys.connectedPlanarDrawing_edgeUpper
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T17:38:16.551771+00:00
-- url     : https://prove2.me/theorems/58115d6d-d07e-4fe8-a305-b4b7a1897190
-- title:
--   Planar edge bound for connected drawings
-- statement:
--   Every connected simple graph on at least three vertices with the supplied crossing-free drawing has at most 3V − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connectedPlanarDrawing_edgeUpper
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
