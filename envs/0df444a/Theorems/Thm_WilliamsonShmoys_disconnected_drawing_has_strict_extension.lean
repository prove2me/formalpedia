-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_drawing_has_strict_extension
-- name    : WilliamsonShmoys.disconnected_drawing_has_strict_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T11:21:12.759636+00:00
-- url     : https://prove2.me/theorems/138dcbf3-fc2b-43e5-ad95-cffd5fa5f3d0
-- title:
--   A disconnected planar drawing admits a strict drawable extension
-- statement:
--   A drawable finite simple graph on at least three vertices that is disconnected has a strictly larger drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_drawing_has_strict_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V, G < H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
