-- Prove2me | Theorems.Thm_QuantumLTF_Majority_realize_phase_clock_algorithm
-- name    : QuantumLTF.Majority.realize_phase_clock_algorithm
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-23T21:57:36.737774+00:00
-- url     : https://prove2.me/theorems/a69a88b9-0daf-47df-b389-7490e2359004
-- title:
--   Realize a finite phase-query clock algorithm as a qubit oracle circuit
-- statement:
--   A finite-dimensional clock algorithm with N oracle slots, input-independent complex unitary transitions, and worst-case success at least 2/3 can be realized exactly by an oracle circuit over arbitrary one- and two-qubit unitary gates. Each phase-oracle slot acts as the Majority phase oracle on the private query register and as the identity on the public register. The realizing circuit uses at most N Majority bit-oracle queries and outputs the characteristic vector of the learned support.
--
--   This is the operational realization step after the state-conversion proof. The finite workspace is embedded into qubits using clean ancillas; the private-register phase operation is simulated with phase kickback and a control bit; fixed finite-dimensional unitaries and output decoding are implemented by exact unitary synthesis.
-- source:
--   Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Section 4.5.1, equations (129)–(134), with the arbitrary one-/two-qubit gate model of Appendix C.5. Exact synthesis can reuse Prove2Me SuperconductingQC.closure_singleQubit_CNOT_eq_top (24a2c1d0-cb9b-47f1-97be-495311250c8d).

import Mathlib
import Definitions.Def_QuantumLTF_Majority_CompilerModel
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Definitions.Def_QuantumLTF_Sections45_Model

namespace QuantumLTF.Majority

open QAlgorithms QuantumLTF.Membership

theorem realize_phase_clock_algorithm (n k N : ℕ) (ω : Type) [Fintype ω] (hN : 0 < N) :
    let ι := BoundedSupports n k
    let E := EuclideanSpace ℂ ((Fin N × Option ι) ⊕ (Qubits n × ω))
    let O : ι → E ≃ₗᵢ[ℂ] E := fun A => compiler_sign_oracle
      (Sum.elim (fun _ => false) (fun j : Qubits n × ω => majorityBit A.1 j.1))
    let start : E := (((Real.sqrt N)⁻¹ : ℝ) : ℂ) • compiler_left (compiler_clock_start N)
    ∀ U : ℕ → E ≃ₗᵢ[ℂ] E,
      (∀ A, (∑ j, if compiler_success_event A j then
        ‖compiler_clock_run U (O A) N start j‖ ^ 2 else 0) ≥ (2/3 : ℝ)) →
      ∃ (m : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n+1) m)
        (out : Fin n ↪ Fin m), c.queryCount 0 ≤ N ∧ LearnsUpTo (k:=k) c out (2/3) := by sorry

end QuantumLTF.Majority
