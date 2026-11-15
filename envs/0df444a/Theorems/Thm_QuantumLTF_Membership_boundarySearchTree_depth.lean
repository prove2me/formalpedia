-- Prove2me | Theorems.Thm_QuantumLTF_Membership_boundarySearchTree_depth
-- name    : QuantumLTF.Membership.boundarySearchTree_depth
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T02:40:05.983215+00:00
-- url     : https://prove2.me/theorems/1e4822fc-ba20-46da-b4a7-8e83bebe9fbd
-- title:
--   Exact depth of the boundary-search tree
-- statement:
--   The explicit boundary-search decision tree first makes two endpoint queries to determine the orientation and then follows exactly $q$ bisection levels. Its worst-case membership-query depth is therefore $q+2$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 3.1, pp. 21–22 (PDF pp. 22–23).

import Mathlib
import Definitions.Def_QuantumLTF_Membership_boundarySearchTree

namespace QuantumLTF.Membership

/-- The boundary-search tree uses two orientation queries followed by exactly `q` bisection queries. -/
theorem boundarySearchTree_depth {n : ℕ} (p : EuclideanSpace ℝ (Fin n))
    (L : ℝ) (q : ℕ) :
    (boundarySearchTree p L q).depth = q + 2 := by sorry

end QuantumLTF.Membership
