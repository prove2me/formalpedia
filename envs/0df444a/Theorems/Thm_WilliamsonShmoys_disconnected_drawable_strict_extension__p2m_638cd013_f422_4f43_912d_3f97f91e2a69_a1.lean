-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_drawable_strict_extension__p2m_638cd013_f422_4f43_912d_3f97f91e2a69_a1
-- name    : WilliamsonShmoys.disconnected_drawable_strict_extension__p2m_638cd013_f422_4f43_912d_3f97f91e2a69_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:24:37.816982+00:00
-- url     : https://prove2.me/theorems/5393d3db-4535-4872-a14a-1f35d96c3cd8
-- title:
--   A disconnected drawable graph has a strict drawable extension
-- statement:
--   Every disconnected drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable strict supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_drawable_strict_extension__p2m_638cd013_f422_4f43_912d_3f97f91e2a69_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hDisc : ¬ M.Connected) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ N ≠ M ∧ HasPlanarDrawingOn N := by sorry
