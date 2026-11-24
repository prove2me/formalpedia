-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_tomography_ideal_input_56
-- name    : QuantumLTF.Membership.Supplement.tomography_ideal_input_56
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-24T19:24:08.819153+00:00
-- url     : https://prove2.me/theorems/75d2f449-e1a8-4384-b885-f4eae6eb21cf
-- title:
--   Ideal-input gate-efficient tomography and orientation recovery for Theorem 5.6
-- statement:
--   For an unknown real unit vector, construct one fixed tomography procedure on sufficiently many exact copies of its direction state, followed by at most three forward, uncontrolled Gaussian quantum-example queries. It outputs a normalized fixed-point estimate within error $\varepsilon$ with probability at least $73/96$. The number of copies, oracle discretization, quantum gate bound, and reversible classical post-processing bound are those of Theorem 5.6, with constants fixed before all input parameters.
--
--   This is the ideal-input part of the theorem. The noisy-input extension follows from trace-distance stability of every measurement event. The procedure and readout are fixed before the unknown direction and before the oracle's unspecified unitary extension.
--
--   Formalization Note. The conclusion explicitly certifies that the ideal tensor-power input is Hermitian with trace one, and that the complete quantum and reversible-classical transformation is unitary for each valid oracle. These standard physical validity properties are needed when applying the measurement-stability theorem; the list-of-matrices circuit definitions do not carry those certificates as structure fields.
-- source:
--   Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Section 5.4, ideal-input portion of Theorem 5.6 (before Eq. (189)), including the three-query orientation test.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_ForwardOnly
import Definitions.Def_QuantumLTF_Membership_Supplement_IsStateOnSpan
import Definitions.Def_QuantumLTF_Membership_Supplement_dirTensorPow
import Definitions.Def_QuantumLTF_Membership_Supplement_padDensity
import Definitions.Def_QuantumLTF_Membership_Supplement_probMixed

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership QuantumLTF.Example

theorem tomography_ideal_input_56 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ C' : ℝ, 0 < C' ∧ ∃ K' : ℕ,
      ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ K : ℕ, C * n / ε ^ 2 ≤ K → ∀ q : ℕ, c * (n : ℝ) ^ 2 / ε ^ 2 ≤ 2 ^ q →
      ∀ s : ℕ, n ≤ 2 ^ s →
        ∃ (e : ℕ) (cq : OracleCircuit gates12 (fun _ : Fin 1 => n * q + 1) (K * s + e))
          (pp : Circuit gatesRev (K * s + e)) (ℓo fo : ℕ) (ov : Fin n → (Fin ℓo ↪ Fin (K * s + e))),
          Uncontrolled cq ∧ ForwardOnly cq ∧ cq.queryCount 0 ≤ 3 ∧
          (cq.gateCount : ℝ) ≤ C' * (n / ε ^ 2) * (1 + Real.log (1 / ε)) * Real.log n ^ K' ∧
          (pp.size : ℝ) ≤ C' * (n / ε) ^ K' ∧
          ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
            (dirTensorPow s K w).IsHermitian ∧ (dirTensorPow s K w).trace = 1 ∧
          ∀ U : Matrix (Qubits (n * q + 1)) (Qubits (n * q + 1)) ℂ, IsQEX (q := q) w U →
            (pp.unitary * cq.unitary (fun _ => U)) ∈ Matrix.unitaryGroup (Qubits (K*s+e)) ℂ ∧
            open Classical in
            probMixed (pp.unitary * cq.unitary fun _ => U) (padDensity e (dirTensorPow s K w))
              (fun z =>
                let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => readFp (ov i) fo z
                v ≠ 0 ∧ ‖‖v‖⁻¹ • v - w‖ ≤ ε) ≥ 73 / 96 := by sorry

end QuantumLTF.Membership.Supplement
