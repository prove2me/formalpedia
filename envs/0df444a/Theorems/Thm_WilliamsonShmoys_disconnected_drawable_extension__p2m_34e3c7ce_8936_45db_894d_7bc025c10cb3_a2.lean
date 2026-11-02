-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_drawable_extension__p2m_34e3c7ce_8936_45db_894d_7bc025c10cb3_a2
-- name    : WilliamsonShmoys.disconnected_drawable_extension__p2m_34e3c7ce_8936_45db_894d_7bc025c10cb3_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:04:50.667236+00:00
-- url     : https://prove2.me/theorems/37fa9a5a-5453-43d3-9231-e1df50e08028
-- title:
--   A sufficiently large disconnected drawable graph has a drawable strict supergraph
-- statement:
--   A drawable graph on at least three vertices that is disconnected has a drawable strict supergraph on the same vertices. This isolates the edge-addition geometry from the parent; the size condition prevents the empty-vertex counterexample to the earlier version. A proof can redraw the finite components in separated regions and route an arc between two components through the complement, while preserving all conditions in `HasPlanarDrawingOn`. Formalizing that construction is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_drawable_extension__p2m_34e3c7ce_8936_45db_894d_7bc025c10cb3_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V)
    (hDisconnected : ¬ K.Connected) :
    ∃ L : SimpleGraph V, K ≤ L ∧ L ≠ K ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
