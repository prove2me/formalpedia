-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_blocks_cover
-- name    : WilliamsonShmoys.component_blocks_cover
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:08:21.98829+00:00
-- url     : https://prove2.me/theorems/a53f3cfc-2d6c-42f4-8b26-ca0a30ccfa73
-- title:
--   Reachability blocks cover all vertices
-- statement:
--   Each vertex is in its own reachability class by reflexivity, so the union of the image family covers the universal finite set. In the empty case both sides are empty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_blocks_cover
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Reachable] :
    (Finset.univ.image (fun v : V => Finset.univ.filter (fun w : V => G.Reachable v w))).biUnion id = Finset.univ := by sorry
