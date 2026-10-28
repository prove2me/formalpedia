-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_support_ncard_sum
-- name    : WilliamsonShmoys.component_support_ncard_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:34:36.782987+00:00
-- url     : https://prove2.me/theorems/15fd235e-fb21-4c46-b05e-e4471dca71dd
-- title:
--   Connected-component supports partition the vertices
-- statement:
--   The sum of the cardinalities of the connected-component supports is the number of vertices, including isolated vertices. The supports form a partition: each vertex lies in the support of its connected component and in no other component support. This removes the vertex-count identification from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.component_support_ncard_sum
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) :
    (∑ C : K.ConnectedComponent, C.supp.ncard) = Fintype.card V := by sorry
