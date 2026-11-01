-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P03_computation_as_measurement
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P03.computation_as_measurement
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:03:11.084389+00:00
-- url     : https://prove2.me/theorems/0dc1b26a-a2d1-409f-a6f4-178b77c0c771
-- title:
--   §3: convert a quantum computation into an input measurement
-- statement:
--   For any unitary computation U on n input and w work bits, copy the retained n-bit input by CNOT into fresh zero computer memory, then apply U only to that memory. The resulting operator has the measurement decomposition ∑_x |x><x| ⊗ (U X_x), with unitary blocks, where X_x XORs x into the first n memory wires. On |x>|0> its output is |x>U|x,0>. Thus every promised classical input has exactly the same output law and success bound as the original computation. The retained input is preserved coherently; this is basis copying, not cloning of a quantum state.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, PDF p. 16, Paragraph before the important eigenphase example

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF p.16, paragraph before the eigenphase example: copying the input and
running the computation on the copy is a measurement of the retained input.
The block decomposition is on the whole ancillary space, and the original
worst-case output-success bound is preserved on every promised classical input. -/
theorem computation_as_measurement (n w : ℕ)
    (U : Matrix (Qubits (n + w)) (Qubits (n + w)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits (n + w)) ℂ) :
    (∀ x : Qubits n, U * inputXorMatrix w x ∈ Matrix.unitaryGroup (Qubits (n + w)) ℂ) ∧
    ((1 : Matrix (Qubits n) (Qubits n) ℂ) ⊗ₖ U) * copyInputMatrix n w =
      (∑ x : Qubits n, pureDensity (ket x) ⊗ₖ (U * inputXorMatrix w x)) ∧
    (∀ x : Qubits n,
      act (((1 : Matrix (Qubits n) (Qubits n) ℂ) ⊗ₖ U) * copyInputMatrix n w)
        (tensorVec (ket x) (zeroKet (n + w))) =
        tensorVec (ket x) (act U (inputState x w))) ∧
    (∀ (m : ℕ) (out : Fin m ↪ Fin (n + w)) (N : Set (Qubits n))
      (F : Qubits n → Qubits m) (epsilon : ℝ), Computes U out N F epsilon →
      ∀ x ∈ N, 1 - epsilon ≤
        probEvent
          (act (((1 : Matrix (Qubits n) (Qubits n) ℂ) ⊗ₖ U) * copyInputMatrix n w)
            (tensorVec (ket x) (zeroKet (n + w))))
          (fun z => z.2 ∘ out = F x)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P03

end
