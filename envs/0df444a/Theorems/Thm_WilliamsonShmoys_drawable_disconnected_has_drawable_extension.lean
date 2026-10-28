-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_disconnected_has_drawable_extension
-- name    : WilliamsonShmoys.drawable_disconnected_has_drawable_extension
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-27T04:05:55.201092+00:00
-- url     : https://prove2.me/theorems/91283452-619c-4b01-a76e-4511e063e862
-- title:
--   A disconnected drawable graph admits a drawable edge extension
-- statement:
--   Any disconnected graph with a crossing-free drawing on a finite linearly ordered vertex type has a drawable supergraph that is not a subgraph of the original. The new drawable graph can be obtained by adding an edge between components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_disconnected_has_drawable_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hdisc : ¬ Q.Connected) :
    ∃ M : SimpleGraph V,
      Q ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ¬ M ≤ Q := by sorry
