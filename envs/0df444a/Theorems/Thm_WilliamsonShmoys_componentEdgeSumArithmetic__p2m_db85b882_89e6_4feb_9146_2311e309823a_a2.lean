-- Prove2me | Theorems.Thm_WilliamsonShmoys_componentEdgeSumArithmetic__p2m_db85b882_89e6_4feb_9146_2311e309823a_a2
-- name    : WilliamsonShmoys.componentEdgeSumArithmetic__p2m_db85b882_89e6_4feb_9146_2311e309823a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:10:31.766195+00:00
-- url     : https://prove2.me/theorems/d843caa4-7b53-4d39-902b-511034925e08
-- title:
--   Summing component edge bounds
-- statement:
--   For at least two blocks, if their sizes sum to the vertex count, their edge counts sum to the total, and each edge count plus three is at most three times its block size, then the total edge count is at most three times the vertex count minus six. Sum the inequalities to obtain an allowance of at least six, then convert the additive inequality to truncated natural subtraction using the vertex-count hypothesis. This removes the finite-sum arithmetic from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.componentEdgeSumArithmetic__p2m_db85b882_89e6_4feb_9146_2311e309823a_a2
    {V : Type} [Fintype V]
    (C : Finset (Finset V)) (edgeCount : Finset V → Nat) (edgeTotal : Nat)
    (hCcard : 2 ≤ C.card)
    (hVertexSum : (∑ s ∈ C, s.card) = Fintype.card V)
    (hEdgeSum : (∑ s ∈ C, edgeCount s) = edgeTotal)
    (hComponentBound : ∀ s ∈ C, edgeCount s + 3 ≤ 3 * s.card)
    (hn : 3 ≤ Fintype.card V) :
    edgeTotal ≤ 3 * Fintype.card V - 6 := by sorry
