-- Prove2me | Theorems.Thm_QuantumLTF_Membership_affineBoundaryBisect_error
-- name    : QuantumLTF.Membership.affineBoundaryBisect_error
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T11:36:03.850689+00:00
-- url     : https://prove2.me/theorems/974eba7a-7426-4006-b358-19bf457c6e29
-- title:
--   Error bound for affine-line boundary bisection
-- statement:
--   If the boundary height at x lies in the initial interval, affine-line binary search returns an estimate whose error is at most the interval width divided by 2^(q+1).
-- source:
--   Coherent boundary-search accuracy used in Theorem 3.2 of Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib
import Definitions.Def_QuantumLTF_Membership_affineBoundaryBisect
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_height

theorem QuantumLTF.Membership.affineBoundaryBisect_error {n : ℕ}
    (w p x : EuclideanSpace ℝ (Fin n)) (θ : ℝ) (q : ℕ) (lo hi : ℝ)
    (ha : inner ℝ w p ≠ 0)
    (hlo : lo ≤ height w θ p x) (hhi : height w θ p x ≤ hi) :
    |(affineBoundaryBisect p x (sgn (inner ℝ w p)) q lo hi).run (ltf w θ) -
      height w θ p x| ≤ (hi - lo) / (2 : ℝ) ^ (q + 1) := by sorry
