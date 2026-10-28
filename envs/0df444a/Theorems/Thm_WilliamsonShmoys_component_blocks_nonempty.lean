-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_blocks_nonempty
-- name    : WilliamsonShmoys.component_blocks_nonempty
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:06:52.646008+00:00
-- url     : https://prove2.me/theorems/48d08ef2-ae32-481e-8cf1-27bfa37d9a0a
-- title:
--   Reachability blocks are nonempty
-- statement:
--   Every block in the image contains its representative, by reflexivity of graph reachability. When the vertex type is empty, there are no blocks and the assertion is vacuous.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_blocks_nonempty
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Reachable] :
    ∀ C ∈ Finset.univ.image (fun v : V => Finset.univ.filter (fun w : V => G.Reachable v w)), C.Nonempty := by sorry
