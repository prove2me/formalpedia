-- Prove2me | Theorems.Thm_SimpleGraph_edgeSet_ncard_mono__p2m_e3ce4704_f609_45f0_9a05_cff1f4f992c7_a1
-- name    : SimpleGraph.edgeSet_ncard_mono__p2m_e3ce4704_f609_45f0_9a05_cff1f4f992c7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:36:27.704437+00:00
-- url     : https://prove2.me/theorems/c20c7d4c-2df9-474a-b3e8-40a69c4c274b
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For finite vertex types, inclusion of simple graphs implies inclusion of their edge sets and hence monotonicity of the edge-set cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem SimpleGraph.edgeSet_ncard_mono__p2m_e3ce4704_f609_45f0_9a05_cff1f4f992c7_a1 {V : Type} [Fintype V] (G H : SimpleGraph V) (hGH : G ≤ H) : G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
