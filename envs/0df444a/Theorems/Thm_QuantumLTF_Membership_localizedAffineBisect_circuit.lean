-- Prove2me | Theorems.Thm_QuantumLTF_Membership_localizedAffineBisect_circuit
-- name    : QuantumLTF.Membership.localizedAffineBisect_circuit
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-15T20:10:40.461212+00:00
-- url     : https://prove2.me/theorems/dea77a82-bdb8-4f24-adfc-8091d9a06024
-- title:
--   Reversible circuit for localized affine bisection
-- statement:
--   Assume the reference point $p$ and initial estimate $\widetilde h_p(0)$ have the fixed-point formats stipulated in Theorem 3.2. For every number $q$ of bisection rounds, the localized affine-bisection computation has a reversible implementation over NOT, CNOT, and Toffoli gates. It uses at most $2q$ membership-oracle calls, including uncomputation, and polynomially many elementary gates and value bits. On every grid basis state it returns exactly the dyadic value produced by the classical localized bisection tree.
--
--   This is the circuit-synthesis component of Theorem 3.2; numerical approximation of the true height is handled separately by the uniform bisection-error theorem.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, proof of Theorem 3.2, pp. 24–26 (PDF pp. 25–27), especially the reversible bisection rounds and uncomputation.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_affineBoundaryBisect
import Definitions.Def_QuantumLTF_Membership_memOracle
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_rho
import Definitions.Def_QuantumLTF_Membership_IsFp
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gridVec
import Definitions.Def_QuantumLTF_Membership_regBasis

namespace QuantumLTF.Membership

open QAlgorithms

theorem localizedAffineBisect_circuit (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∀ (b q : ℕ) (p : EuclideanSpace ℝ (Fin n)) (Bp fp : ℕ), (Bp : ℝ) ≤ C₁ * Real.log n →
        (∀ i, IsFp Bp fp (p i)) →
      ∀ (s : ℤ) (htil : ℝ) (Bh fh : ℕ), (Bh : ℝ) ≤ C₂ * Real.log (1 / ε) → IsFp Bh fh htil →
        ∃ (ℓ f Vb Vf W : ℕ)
          (c : OracleCircuit gatesRev (fun _ : Fin 1 => n * ℓ + 1) (n * b + Vb + W)),
          Uncontrolled c ∧
          c.queryCount 0 ≤ 2 * q ∧
          (c.gateCount : ℝ) ≤ C * n * (b + Real.log n + Real.log (1 / ε) + q) ^ 2 * (q + 1) ∧
          (Vb : ℝ) ≤ C * (Real.log (1 / ε) + q + 1) ∧
          ∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ), ‖w‖ = 1 →
            1 / 10 ≤ |inner ℝ w p| → |inner ℝ w p| ≤ 3 → s = sgn (inner ℝ w p) →
            |htil - height w θ p 0| ≤ ε / 100 →
            ∃ Htil : (Fin n → Qubits b) → Qubits Vb,
              (∀ x, act (c.unitary fun _ => memOracle n ℓ f w θ)
                  (ket (regBasis n b Vb W x fun _ => false)) =
                ket (regBasis n b Vb W x (Htil x))) ∧
              ∀ x, fpVal Vb Vf (Htil x) =
                (affineBoundaryBisect p (rho n • gridVec n b x) s q
                  (htil - 1 / 4) (htil + 1 / 4)).run (ltf w θ) := by sorry

end QuantumLTF.Membership
