-- Prove2me | Theorems.Thm_SimpleGraph_edgeSet_ncard_mono_for_4be75fe8
-- name    : SimpleGraph.edgeSet_ncard_mono_for_4be75fe8
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:45:39.312973+00:00
-- url     : https://prove2.me/theorems/52777e18-6531-45cc-ac1d-73ef09cfaa4b
-- title:
--   Monotonicity of finite graph edge counts
-- statement:
--   For finite graphs on the same vertex type, edge inclusion implies that the first graph has no more edges than the second.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem SimpleGraph.edgeSet_ncard_mono_for_4be75fe8
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
