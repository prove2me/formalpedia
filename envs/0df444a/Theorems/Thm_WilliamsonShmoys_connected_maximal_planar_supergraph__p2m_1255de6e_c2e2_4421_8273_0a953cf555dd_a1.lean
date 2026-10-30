-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_maximal_planar_supergraph__p2m_1255de6e_c2e2_4421_8273_0a953cf555dd_a1
-- name    : WilliamsonShmoys.connected_maximal_planar_supergraph__p2m_1255de6e_c2e2_4421_8273_0a953cf555dd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:08:53.664798+00:00
-- url     : https://prove2.me/theorems/cc5cc3f2-db05-4ace-b001-4997052bea6e
-- title:
--   Maximal planar graphs are connected
-- statement:
--   A planar graph on at least three vertices that is maximal among planar supergraphs on the same vertex type is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_maximal_planar_supergraph__p2m_1255de6e_c2e2_4421_8273_0a953cf555dd_a1 {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J ≤ H) :
    H.Connected := by sorry
