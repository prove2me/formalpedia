-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph__p2m_11b8d141_5db8_4e85_8178_19adf7dd7abd_a1
-- name    : WilliamsonShmoys.connected_planar_supergraph__p2m_11b8d141_5db8_4e85_8178_19adf7dd7abd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T12:28:37.228694+00:00
-- url     : https://prove2.me/theorems/7209092e-3d86-48ee-86e8-1886eaa54774
-- title:
--   Connected drawable supergraph on the same vertices
-- statement:
--   Any drawable finite simple graph on at least three vertices admits a connected drawable supergraph on the same vertices whose edge count is no smaller. This removes disconnectedness from the parent argument. The route is to connect components through the complement of the finite drawing, preserving the original edges and vertex set; the lower bound of three vertices is preserved, including at equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_supergraph__p2m_11b8d141_5db8_4e85_8178_19adf7dd7abd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.Connected ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
