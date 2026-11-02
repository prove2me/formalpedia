-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeFinset_card_mono__p2m_cd005786_48c0_47b3_9c83_f93270ee4ea9_a2
-- name    : WilliamsonShmoys.edgeFinset_card_mono__p2m_cd005786_48c0_47b3_9c83_f93270ee4ea9_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:56:13.411708+00:00
-- url     : https://prove2.me/theorems/74356c88-8f19-4ad9-babf-6b0db9c7b2a3
-- title:
--   Edge count is monotone under adjacency inclusion
-- statement:
--   For finite simple graphs on the same finite linearly ordered vertex type, if every adjacency of G is an adjacency of H, then G has no more edges than H.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.edgeFinset_card_mono__p2m_cd005786_48c0_47b3_9c83_f93270ee4ea9_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (hsub : forall u v, G.Adj u v -> H.Adj u v) :
    letI : forall K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
    G.edgeFinset.card <= H.edgeFinset.card := by sorry
