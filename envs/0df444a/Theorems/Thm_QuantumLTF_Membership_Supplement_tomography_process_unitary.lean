-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_tomography_process_unitary
-- name    : QuantumLTF.Membership.Supplement.tomography_process_unitary
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-24T23:24:26.131147+00:00
-- url     : https://prove2.me/theorems/5a5fd3eb-ab03-4f72-870b-6995d6a30ac2
-- title:
--   Unitarity of an uncontrolled tomography circuit with reversible post-processing
-- statement:
--   Let $c_q$ be an uncontrolled quantum oracle circuit on $n$ qubits, using unitary elementary gates on at most two wires. Let $p$ be a reversible circuit on the same register using NOT, CNOT, and Toffoli gates. If every supplied oracle matrix $U_k$ is unitary, then the combined process is unitary:
--
--   $$p\,c_q(U_1,\ldots,U_r)\in\mathrm U(2^n).$$
--
--   This verifies the physical validity of the circuit interface used for Theorem 5.6. It applies to every circuit of that interface and does not assert the existence or resource bounds of the tomography algorithm.
-- source:
--   Supporting circuit-validity lemma for Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5.4, Theorem 5.6; NOT/CNOT/Toffoli reversible post-processing.

import Mathlib
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
open QAlgorithms QuantumLTF.Membership

theorem QuantumLTF.Membership.Supplement.tomography_process_unitary {r n : ℕ} {a : Fin r → ℕ}
    (cq : OracleCircuit gates12 a n) (hunc : Uncontrolled cq) (pp : Circuit gatesRev n)
    (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ)
    (hU : ∀ k, orc k ∈ Matrix.unitaryGroup (Qubits (a k)) ℂ) :
    pp.unitary * cq.unitary orc ∈ Matrix.unitaryGroup (Qubits n) ℂ := by sorry
