-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_b967a95f_e156_4a9a_acf3_4c05427be8a4_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_b967a95f_e156_4a9a_acf3_4c05427be8a4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:04:12.420884+00:00
-- url     : https://prove2.me/theorems/2224d641-face-441b-a11e-e0d6c885d879
-- title:
--   Apply the connected planar edge estimate with small-component bounds
-- statement:
--   Given the assumed connected planar edge estimate, every finite connected planar graph satisfies that estimate at size at least three and has at most as many edges as vertices when its size is below three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_b967a95f_e156_4a9a_acf3_4c05427be8a4_a1
    {U : Type} [Fintype U] [LinearOrder U]
    (hconnected : ∀ {W : Type} [Fintype W] [LinearOrder W]
      (N : SimpleGraph W) (dN : DecidableRel N.Adj),
      HasPlanarDrawingOn N → N.Connected → 3 ≤ Fintype.card W →
      N.edgeFinset.card ≤ 3 * Fintype.card W - 6)
    (N : SimpleGraph U) (dN : DecidableRel N.Adj)
    (hN : HasPlanarDrawingOn N) (hc : N.Connected) :
    (3 ≤ Fintype.card U → N.edgeFinset.card ≤ 3 * Fintype.card U - 6) ∧
    (Fintype.card U < 3 → N.edgeFinset.card ≤ Fintype.card U) := by sorry
