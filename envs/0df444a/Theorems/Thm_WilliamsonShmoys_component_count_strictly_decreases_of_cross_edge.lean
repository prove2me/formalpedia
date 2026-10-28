-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_count_strictly_decreases_of_cross_edge
-- name    : WilliamsonShmoys.component_count_strictly_decreases_of_cross_edge
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:22:02.121992+00:00
-- url     : https://prove2.me/theorems/0d522c06-0a81-4477-bd17-8e27f44e18f0
-- title:
--   A cross-component edge strictly decreases the component count
-- statement:
--   For finite vertex types, if K contains G and has an edge between vertices not previously connected in G, then K has strictly fewer connected components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.component_count_strictly_decreases_of_cross_edge
    {V : Type} [Fintype V]
    (G K : SimpleGraph V) (hGK : G ≤ K)
    (u v : V) (hnot : ¬ G.Reachable u v) (hadj : K.Adj u v) :
    Nat.card K.ConnectedComponent < Nat.card G.ConnectedComponent := by sorry
