-- Prove2me | Theorems.Thm_QuantumLTF_Membership_affineBoundaryBisect_run
-- name    : QuantumLTF.Membership.affineBoundaryBisect_run
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T11:33:18.179459+00:00
-- url     : https://prove2.me/theorems/205d515b-c16a-4ac7-9da9-d1d60a3bd3f6
-- title:
--   Execution semantics of affine-line boundary bisection
-- statement:
--   Running affine-line orientation-aware bisection against the membership oracle has exactly the scalar binary-search semantics for the boundary height at the chosen grid point x.
-- source:
--   Coherent boundary-search component of Theorem 3.2 in Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib
import Definitions.Def_QuantumLTF_Membership_affineBoundaryBisect
import Definitions.Def_QuantumLTF_Membership_orientedBisectValue
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_height

theorem QuantumLTF.Membership.affineBoundaryBisect_run {n : ℕ}
    (w p x : EuclideanSpace ℝ (Fin n)) (θ : ℝ) (q : ℕ) (lo hi : ℝ)
    (ha : inner ℝ w p ≠ 0) :
    (affineBoundaryBisect p x (sgn (inner ℝ w p)) q lo hi).run (ltf w θ) =
      orientedBisectValue (sgn (inner ℝ w p)) q lo hi (height w θ p x) := by sorry
