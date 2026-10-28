-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_extension_of_planar_augmentation
-- name    : WilliamsonShmoys.connected_extension_of_planar_augmentation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:33:18.427572+00:00
-- url     : https://prove2.me/theorems/9866a157-1cb8-4c8c-a165-a1a6e642fa3e
-- title:
--   Iterate planar edge augmentation to a connected extension
-- statement:
--   If every disconnected planar graph on the given finite vertex type admits a planar edge-increasing supergraph, then M has a connected planar supergraph containing all its edges. Maximize the edge count among planar supergraphs containing M; the step premise rules out a disconnected maximizer, and edge inclusion proves the count inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_extension_of_planar_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hstep : ∀ G : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn G →
      ¬ G.Connected →
      ∃ H : SimpleGraph V,
        (∀ u v, G.Adj u v → H.Adj u v) ∧
        WilliamsonShmoys.HasPlanarDrawingOn H ∧
        G.edgeSet.ncard < H.edgeSet.ncard) :
    ∃ N : SimpleGraph V,
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      N.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard := by
  sorry
