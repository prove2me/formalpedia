-- Prove2me | Theorems.Thm_QuantumLTF_Membership_QueryTree_run_map
-- name    : QuantumLTF.Membership.QueryTree_run_map
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T02:44:15.056448+00:00
-- url     : https://prove2.me/theorems/3c6a32b7-91db-40c2-9436-b7cbe06e12b3
-- title:
--   Running a mapped query tree
-- statement:
--   Replacing every leaf output $a$ of a deterministic membership-query tree by $g(a)$ does not alter the queries or branches. Running the mapped tree returns $g$ applied to the output of the original tree.
-- source:
--   Structural property of the QueryTree implementation used for Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, Theorem 3.1.

import Mathlib
import Definitions.Def_QuantumLTF_Membership_boundarySearchTree

namespace QuantumLTF.Membership

/-- Mapping every leaf output commutes with running a query tree. -/
theorem QueryTree_run_map {n : ℕ} {α β : Type} (g : α → β)
    (T : QueryTree n α) (f : EuclideanSpace ℝ (Fin n) → ℤ) :
    (T.map g).run f = g (T.run f) := by sorry

end QuantumLTF.Membership
