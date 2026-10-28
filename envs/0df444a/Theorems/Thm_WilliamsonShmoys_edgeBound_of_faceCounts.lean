-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeBound_of_faceCounts
-- name    : WilliamsonShmoys.edgeBound_of_faceCounts
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:29:03.411502+00:00
-- url     : https://prove2.me/theorems/62820361-bc10-4a24-a463-6083dec6bcfe
-- title:
--   Planar edge bound from face counts
-- statement:
--   Euler’s equation, total facial boundary length 2E, and length at least three for every face imply E + 6 ≤ 3|V|. Prove by summing the face lower bounds and substituting Euler’s equation; this removes the finite counting work from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edgeBound_of_faceCounts
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hFaces : ∃ (F : Nat) (faceLength : Fin F → Nat),
      Fintype.card V + F = G.edgeSet.ncard + 2 ∧
      (∑ f : Fin F, faceLength f) = 2 * G.edgeSet.ncard ∧
      ∀ f : Fin F, 3 <= faceLength f) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
