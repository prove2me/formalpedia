-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_blocks_disjoint
-- name    : WilliamsonShmoys.component_blocks_disjoint
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:07:48.179559+00:00
-- url     : https://prove2.me/theorems/fb0c4e46-608c-4348-8a2b-d7be8b75f972
-- title:
--   Distinct reachability blocks are disjoint
-- statement:
--   If two reachability classes share a vertex, symmetry and transitivity imply that their representatives are mutually reachable, so the two supports are equal. Thus distinct supports are disjoint.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_blocks_disjoint
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Reachable] :
    ∀ C ∈ Finset.univ.image (fun v : V => Finset.univ.filter (fun w : V => G.Reachable v w)),
      ∀ D ∈ Finset.univ.image (fun v : V => Finset.univ.filter (fun w : V => G.Reachable v w)),
        C ≠ D → Disjoint C D := by sorry
