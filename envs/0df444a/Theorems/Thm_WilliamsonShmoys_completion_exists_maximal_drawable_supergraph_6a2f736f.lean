-- Prove2me | Theorems.Thm_WilliamsonShmoys_completion_exists_maximal_drawable_supergraph_6a2f736f
-- name    : WilliamsonShmoys.completion_exists_maximal_drawable_supergraph_6a2f736f
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:26:39.831235+00:00
-- url     : https://prove2.me/theorems/7a390b56-5c36-430c-b82b-136e1405d945
-- title:
--   Finite maximal drawable extension
-- statement:
--   Among the finitely many simple graphs on V that extend G and admit a drawing, choose one with maximum edge count. No strict drawable extension can then exist. The statement does not require the original graph to be connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.completion_exists_maximal_drawable_supergraph_6a2f736f
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ¬ ∃ H : SimpleGraph V,
          K < H ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
