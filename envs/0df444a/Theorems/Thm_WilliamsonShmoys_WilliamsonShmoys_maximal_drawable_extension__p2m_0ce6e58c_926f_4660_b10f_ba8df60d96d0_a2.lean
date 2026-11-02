-- Prove2me | Theorems.Thm_WilliamsonShmoys_WilliamsonShmoys_maximal_drawable_extension__p2m_0ce6e58c_926f_4660_b10f_ba8df60d96d0_a2
-- name    : WilliamsonShmoys.WilliamsonShmoys_maximal_drawable_extension__p2m_0ce6e58c_926f_4660_b10f_ba8df60d96d0_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:42:25.142199+00:00
-- url     : https://prove2.me/theorems/3bb112e2-2df9-4e3a-a157-84b2375941f4
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable finite graph is contained in a drawable supergraph maximal under inclusion on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.WilliamsonShmoys_maximal_drawable_extension__p2m_0ce6e58c_926f_4660_b10f_ba8df60d96d0_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V, P ≤ Q ∧ HasPlanarDrawingOn Q ∧
      ∀ R : SimpleGraph V, Q ≤ R → HasPlanarDrawingOn R → R ≤ Q := by sorry
