-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_local_sum_bound__p2m_2f886b64_45e5_4692_a31b_5084b02f539f_a1
-- name    : WilliamsonShmoys.component_local_sum_bound__p2m_2f886b64_45e5_4692_a31b_5084b02f539f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:13:28.471208+00:00
-- url     : https://prove2.me/theorems/b7f5e6d4-c2f1-4299-bdb1-5ab76d086eef
-- title:
--   Sum the component-local bounds
-- statement:
--   The sum of the local edge-plus-deficit bounds is at most three times the sum of the component vertex counts.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.component_local_sum_bound__p2m_2f886b64_45e5_4692_a31b_5084b02f539f_a1 {V : Type} [Fintype V] (M : SimpleGraph V) (parts : Finset (Finset V)) (hlocal : ∀ C, C ∈ parts → (M.induce (C : Set V)).edgeSet.ncard + (if 3 ≤ Fintype.card {x : V // x ∈ C} then 6 else if Fintype.card {x : V // x ∈ C} = 2 then 5 else 3) ≤ 3 * Fintype.card {x : V // x ∈ C}) : (∑ C ∈ parts, ((M.induce (C : Set V)).edgeSet.ncard + (if 3 ≤ Fintype.card {x : V // x ∈ C} then 6 else if Fintype.card {x : V // x ∈ C} = 2 then 5 else 3))) ≤ 3 * ∑ C ∈ parts, Fintype.card {x : V // x ∈ C} := by sorry
