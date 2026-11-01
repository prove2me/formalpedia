-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeFinset_card_mono_of_subgraph__p2m_602c691a_8d1a_4dfe_88c6_7f0f95c89b91_a1
-- name    : WilliamsonShmoys.edgeFinset_card_mono_of_subgraph__p2m_602c691a_8d1a_4dfe_88c6_7f0f95c89b91_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:15:33.044864+00:00
-- url     : https://prove2.me/theorems/9e968c31-4c07-4d61-9fe9-8223899cb1e9
-- title:
--   Edge count is monotone under subgraph inclusion
-- statement:
--   If one finite simple graph is a subgraph of another on the same vertex type, its number of edges is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edgeFinset_card_mono_of_subgraph__p2m_602c691a_8d1a_4dfe_88c6_7f0f95c89b91_a1
    {V : Type} [Fintype V]
    (G H : SimpleGraph V) (hGH : G ≤ H) :
    (letI : DecidableRel G.Adj := Classical.decRel _
     letI : DecidableRel H.Adj := Classical.decRel _
     G.edgeFinset.card ≤ H.edgeFinset.card) := by sorry
