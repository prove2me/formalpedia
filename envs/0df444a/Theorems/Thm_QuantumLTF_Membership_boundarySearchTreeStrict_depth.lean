-- Prove2me | Theorems.Thm_QuantumLTF_Membership_boundarySearchTreeStrict_depth
-- name    : QuantumLTF.Membership.boundarySearchTreeStrict_depth
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T03:30:11.510009+00:00
-- url     : https://prove2.me/theorems/569a66a8-1fa7-41de-a055-da78b79bc346
-- title:
--   Depth of the strict boundary-search tree
-- statement:
--   The corrected boundary-search tree uses exactly two orientation queries followed by $q$ bisection queries, so every root-to-leaf path has depth $q+2$.
-- source:
--   Supporting lemma for Theorem 3.1 of Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib
import Definitions.Def_QuantumLTF_Membership_boundarySearchTreeStrict

theorem QuantumLTF.Membership.boundarySearchTreeStrict_depth {n : ℕ}
    (p : EuclideanSpace ℝ (Fin n)) (L : ℝ) (q : ℕ) :
    (boundarySearchTreeStrict p L q).depth = q + 2 := by sorry
