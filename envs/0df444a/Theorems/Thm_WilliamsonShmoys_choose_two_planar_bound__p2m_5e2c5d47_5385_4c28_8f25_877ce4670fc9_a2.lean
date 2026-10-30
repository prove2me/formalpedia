-- Prove2me | Theorems.Thm_WilliamsonShmoys_choose_two_planar_bound__p2m_5e2c5d47_5385_4c28_8f25_877ce4670fc9_a2
-- name    : WilliamsonShmoys.choose_two_planar_bound__p2m_5e2c5d47_5385_4c28_8f25_877ce4670fc9_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:31:10.364652+00:00
-- url     : https://prove2.me/theorems/e7a87211-648c-4ea4-b64e-227a146d08f8
-- title:
--   The complete graph edge bound forces at most four vertices
-- statement:
--   For a natural number at least three, if its complete-graph edge count satisfies the planar edge bound, then the number is at most four. The proof reduces `n.choose 2` to a product and shows every `n ≥ 5` violates the inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.choose_two_planar_bound__p2m_5e2c5d47_5385_4c28_8f25_877ce4670fc9_a2
    (n : ℕ)
    (hcard : 3 ≤ n)
    (hedges : n.choose 2 ≤ 3 * n - 6) :
    n ≤ 4 := by sorry
