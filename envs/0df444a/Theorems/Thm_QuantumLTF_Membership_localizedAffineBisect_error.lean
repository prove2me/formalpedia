-- Prove2me | Theorems.Thm_QuantumLTF_Membership_localizedAffineBisect_error
-- name    : QuantumLTF.Membership.localizedAffineBisect_error
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T19:04:35.729122+00:00
-- url     : https://prove2.me/theorems/a8c26e17-a524-4644-9d47-b918ed7a7953
-- title:
--   Uniform local bisection error on the scaled grid
-- statement:
--   Using the fixed interval of radius one quarter around the estimated offset, q affine-line bisection updates approximate every scaled-grid height with error at most 2^(-q-2).
-- source:
--   Uniform local binary search in Theorem 3.2 of Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_affineBoundaryBisect
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_rho
import Definitions.Def_QuantumLTF_Membership_gridVec
open QAlgorithms

theorem QuantumLTF.Membership.localizedAffineBisect_error {n b : ℕ}
    (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (w p : EuclideanSpace ℝ (Fin n)) (θ htil : ℝ)
    (hw : ‖w‖ = 1) (ha : 1 / 10 ≤ |inner ℝ w p|)
    (hhtil : |htil - height w θ p 0| ≤ ε / 100)
    (x : Fin n → Qubits b) (q : ℕ) :
    |(affineBoundaryBisect p (rho n • gridVec n b x) (sgn (inner ℝ w p)) q
        (htil - 1 / 4) (htil + 1 / 4)).run (ltf w θ) -
      height w θ p (rho n • gridVec n b x)| ≤ 1 / (2 : ℝ) ^ (q + 2) := by sorry
