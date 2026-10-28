-- Prove2me | Theorems.Thm_SimpleGraph_edgeSet_ncard_mono_9538c7a8_17aa_406f_ad1c_e0bdce92c761
-- name    : SimpleGraph.edgeSet_ncard_mono_9538c7a8_17aa_406f_ad1c_e0bdce92c761
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:56:22.786268+00:00
-- url     : https://prove2.me/theorems/911a9321-5900-4005-9e01-e677d8a6bcb6
-- title:
--   Edge-set cardinality is monotone under graph inclusion
-- statement:
--   For finite graphs on the same vertex type, graph inclusion implies that the smaller graph has no more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem SimpleGraph.edgeSet_ncard_mono_9538c7a8_17aa_406f_ad1c_e0bdce92c761
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
