-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_maximal_extension__p2m_81eecf30_e96c_499d_b4eb_13964c396f7c_a2
-- name    : WilliamsonShmoys.connected_planar_maximal_extension__p2m_81eecf30_e96c_499d_b4eb_13964c396f7c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:10:26.243776+00:00
-- url     : https://prove2.me/theorems/d907868f-a17b-474c-8cf2-9084ceb6d5c7
-- title:
--   Maximal planar extension of a connected planar graph
-- statement:
--   A connected planar graph on a finite vertex type has a connected planar supergraph that is maximal among planar supergraphs on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_maximal_extension__p2m_81eecf30_e96c_499d_b4eb_13964c396f7c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (C : SimpleGraph V) (hC : WilliamsonShmoys.HasPlanarDrawingOn C)
    (hconn : C.Connected) :
    ∃ H : SimpleGraph V,
      C ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        (letI : DecidableRel K.Adj := Classical.decRel _;
         H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by sorry
