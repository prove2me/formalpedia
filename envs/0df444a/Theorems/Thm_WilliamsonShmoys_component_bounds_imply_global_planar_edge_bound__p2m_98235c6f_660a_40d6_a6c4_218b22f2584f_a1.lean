-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_bounds_imply_global_planar_edge_bound__p2m_98235c6f_660a_40d6_a6c4_218b22f2584f_a1
-- name    : WilliamsonShmoys.component_bounds_imply_global_planar_edge_bound__p2m_98235c6f_660a_40d6_a6c4_218b22f2584f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:03:20.921213+00:00
-- url     : https://prove2.me/theorems/2f886b64-45e5-4692-a31b-5084b02f539f
-- title:
--   Sum component deficits to obtain the global edge bound
-- statement:
--   Given the local deficit bounds and edge aggregation, the global edge bound follows by summing over the disjoint cover. The cover identifies the sum of component vertex counts with the total vertex count. Nonempty parts and total size at least three ensure the sum of the size-dependent deficits is at least six. The remaining proof is finite-sum and natural-number arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.component_bounds_imply_global_planar_edge_bound__p2m_98235c6f_660a_40d6_a6c4_218b22f2584f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (parts : Finset (Finset V))
    (hcover : ∀ v, ∃ C, C ∈ parts ∧ v ∈ C)
    (hnonempty : ∀ C, C ∈ parts → C.Nonempty)
    (hdisjoint : ∀ C, C ∈ parts → ∀ D, D ∈ parts → C ≠ D → Disjoint C D)
    (hcard : 3 ≤ Fintype.card V)
    (hlocal : ∀ C, C ∈ parts →
      (M.induce (C : Set V)).edgeSet.ncard +
        (if 3 ≤ Fintype.card {x : V // x ∈ C} then 6
         else if Fintype.card {x : V // x ∈ C} = 2 then 5 else 3)
        ≤ 3 * Fintype.card {x : V // x ∈ C})
    (hagg : M.edgeSet.ncard ≤
      ∑ C ∈ parts, (M.induce (C : Set V)).edgeSet.ncard) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
