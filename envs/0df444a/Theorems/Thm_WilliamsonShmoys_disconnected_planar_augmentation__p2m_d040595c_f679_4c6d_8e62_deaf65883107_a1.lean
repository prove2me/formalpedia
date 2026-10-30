-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_augmentation__p2m_d040595c_f679_4c6d_8e62_deaf65883107_a1
-- name    : WilliamsonShmoys.disconnected_planar_augmentation__p2m_d040595c_f679_4c6d_8e62_deaf65883107_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:49:51.913362+00:00
-- url     : https://prove2.me/theorems/b9f24409-3d4f-491d-a7d1-53a879b4d6a5
-- title:
--   Augmenting a disconnected drawable graph
-- statement:
--   If a finite drawable graph on at least three vertices is disconnected, it has a strictly larger drawable supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_planar_augmentation__p2m_d040595c_f679_4c6d_8e62_deaf65883107_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hDisc : ¬ M.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ N ≠ M ∧ WilliamsonShmoys.HasPlanarDrawingOn N := by sorry
