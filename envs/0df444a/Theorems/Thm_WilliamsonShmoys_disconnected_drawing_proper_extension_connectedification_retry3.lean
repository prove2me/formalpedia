-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_drawing_proper_extension_connectedification_retry3
-- name    : WilliamsonShmoys.disconnected_drawing_proper_extension_connectedification_retry3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:18:34.283608+00:00
-- url     : https://prove2.me/theorems/ec1fa3a1-e9a2-4972-a5ba-131974b9d109
-- title:
--   A disconnected drawing admits a proper drawable extension
-- statement:
--   A disconnected graph with a crossing-free drawing on at least three vertices has a proper drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_drawing_proper_extension_connectedification_retry3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hNotConnected : ¬ H.Connected) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      K ≠ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
