-- Prove2me | Theorems.Thm_SimpleGraph_edgeSet_ncard_mono__p2m_62578b33_7986_4643_ae9c_c0cb30164949_a1
-- name    : SimpleGraph.edgeSet_ncard_mono__p2m_62578b33_7986_4643_ae9c_c0cb30164949_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:06:55.426714+00:00
-- url     : https://prove2.me/theorems/5ab4d594-ce18-4918-b37a-ec7926e91486
-- title:
--   Monotonicity of finite graph edge counts
-- statement:
--   On a finite vertex type, inclusion of simple graphs implies monotonicity of the cardinality of their edge sets.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem SimpleGraph.edgeSet_ncard_mono__p2m_62578b33_7986_4643_ae9c_c0cb30164949_a1
    {V : Type} [Fintype V] (G H : SimpleGraph V) (h : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
