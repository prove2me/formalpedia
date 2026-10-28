-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_repair_20261028_maximal_extension
-- name    : WilliamsonShmoys.connected_planar_edge_count_repair_20261028_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:11:29.35379+00:00
-- url     : https://prove2.me/theorems/4a03bf38-b900-4004-a3fd-a24d8e0e1e5e
-- title:
--   Finite maximal planar extension
-- statement:
--   Any finite planar graph on the given vertex type has a planar supergraph that is maximal under edge inclusion among planar graphs on that same vertex type. The extra connectedness and size hypotheses are retained for compatibility with the target; the finite maximality argument itself does not require them.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_count_repair_20261028_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hConnected : H.Connected)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
