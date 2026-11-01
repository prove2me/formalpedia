-- Prove2me | Theorems.Thm_WilliamsonShmoys_bridge_extension_strict_edgeSet__p2m_1743449e_70b2_453d_82e4_df1f7d1e75bd_a3
-- name    : WilliamsonShmoys.bridge_extension_strict_edgeSet__p2m_1743449e_70b2_453d_82e4_df1f7d1e75bd_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:09:15.771378+00:00
-- url     : https://prove2.me/theorems/f30a3e63-593e-4761-8c47-8d21d3e62ad2
-- title:
--   A bridge between unreachable vertices is a new edge
-- statement:
--   If L contains every edge of K and has an edge between vertices unreachable in K, then L has a strictly larger edge set. The proof uses edge-set membership to show that equality of edge sets would make the endpoints adjacent, and therefore reachable, in K.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.bridge_extension_strict_edgeSet__p2m_1743449e_70b2_453d_82e4_df1f7d1e75bd_a3
    {V : Type} [DecidableEq V] {K L : SimpleGraph V}
    (hsub : K.edgeSet ⊆ L.edgeSet)
    {u v : V} (hnot : ¬ K.Reachable u v) (hadj : L.Adj u v) :
    K.edgeSet ⊂ L.edgeSet := by sorry
