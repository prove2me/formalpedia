-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_has_unreachable_pair__p2m_9ff15d30_8739_4d4c_ada8_35f6650f3988_a1
-- name    : WilliamsonShmoys.disconnected_has_unreachable_pair__p2m_9ff15d30_8739_4d4c_ada8_35f6650f3988_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T06:03:48.794017+00:00
-- url     : https://prove2.me/theorems/be47ae41-5e49-475b-b9cb-c4766dd1028d
-- title:
--   A disconnected graph has an unreachable pair
-- statement:
--   A disconnected graph has a pair of vertices that are not connected by a walk.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_has_unreachable_pair__p2m_9ff15d30_8739_4d4c_ada8_35f6650f3988_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hnot : ¬ K.Connected) : ∃ u v : V, ¬ K.Reachable u v := by sorry
