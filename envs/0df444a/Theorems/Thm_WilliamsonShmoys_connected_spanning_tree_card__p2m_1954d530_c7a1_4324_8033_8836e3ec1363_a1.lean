-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_spanning_tree_card__p2m_1954d530_c7a1_4324_8033_8836e3ec1363_a1
-- name    : WilliamsonShmoys.connected_spanning_tree_card__p2m_1954d530_c7a1_4324_8033_8836e3ec1363_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:35:26.460532+00:00
-- url     : https://prove2.me/theorems/44104116-73f3-493a-bfc6-ce305231db27
-- title:
--   Connected spanning tree with the finite-graph boundary case
-- statement:
--   A finite connected graph either has no vertices and no edges, or contains a connected spanning subgraph with one fewer edge than vertices. The empty case is included explicitly because connectedness may be vacuous there.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_spanning_tree_card__p2m_1954d530_c7a1_4324_8033_8836e3ec1363_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hconnected : H.Connected) :
    (Fintype.card V = 0 ∧ H.edgeSet.ncard = 0) ∨
      ∃ T : SimpleGraph V, T ≤ H ∧ T.Connected ∧
        T.edgeSet.ncard + 1 = Fintype.card V := by sorry
