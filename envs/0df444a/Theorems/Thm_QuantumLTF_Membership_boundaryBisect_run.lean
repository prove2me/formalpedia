-- Prove2me | Theorems.Thm_QuantumLTF_Membership_boundaryBisect_run
-- name    : QuantumLTF.Membership.boundaryBisect_run
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T03:22:04.913207+00:00
-- url     : https://prove2.me/theorems/cfd99499-1e97-48da-98a5-0904fdf3c062
-- title:
--   Execution semantics of orientation-aware boundary bisection
-- statement:
--   Running the orientation-aware bisection query tree against a linear-threshold membership oracle has exactly the scalar recursive semantics of binary search for the boundary height. The orientation is the sign of the nonzero directional inner product.
-- source:
--   Supporting lemma for Theorem 3.1 of Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib
import Definitions.Def_QuantumLTF_Membership_boundarySearchTree
import Definitions.Def_QuantumLTF_Membership_orientedBisectValue
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_height

theorem QuantumLTF.Membership.boundaryBisect_run {n : ℕ}
    (w p : EuclideanSpace ℝ (Fin n)) (θ : ℝ) (q : ℕ) (lo hi : ℝ)
    (ha : inner ℝ w p ≠ 0) :
    (boundaryBisect p (sgn (inner ℝ w p)) q lo hi).run (ltf w θ) =
      orientedBisectValue (sgn (inner ℝ w p)) q lo hi (height w θ p 0) := by sorry
