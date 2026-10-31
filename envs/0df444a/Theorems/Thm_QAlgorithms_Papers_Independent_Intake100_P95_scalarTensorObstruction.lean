-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P95_scalarTensorObstruction
-- name    : QAlgorithms.Papers.Independent.Intake100.P95.scalarTensorObstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:52:43.092824+00:00
-- url     : https://prove2.me/theorems/ee89fb8e-ccb1-4433-beb2-0a4f10115a2f
-- title:
--   The two-qubit scalar tensor has no reversing similarity
-- statement:
--   For two qubits define the particular scalar tensor
--
--   $$T_{0,0}=-\frac{X\otimes X+Y\otimes Y+Z\otimes Z}{2\sqrt3}.$$
--
--   This tensor is nonzero. For every nonzero complex scalar $c$ and every invertible complex $4\times4$ matrix $S$,
--
--   $$S(cT_{0,0})S^{-1}\ne-cT_{0,0}.$$
--
--   Thus even unrestricted similarities cannot sign-invert the specific scalar tensor or any nonzero multiple of it. The assertion does not extend to all rank-zero tensors in larger systems.
-- source:
--   Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks, arXiv:quant-ph/0610061v1, PDF p. 7, (36): the two-qubit scalar XXX tensor cannot be sign inverted

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95

namespace QAlgorithms.Papers.Independent.Intake100.P95

open scoped BigOperators

open QAlgorithms.Papers.Independent.Information100.P32 (Op evolution)

open QAlgorithms.Papers.Independent.Advance50.P38 (comm realHSPairing)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Claimed50.P03 (wordMatrix wordSupport)

noncomputable section

/-- (36), PDF p.7: the specific two-qubit scalar QAlgorithms.kronAll
T_00=-(XX+YY+ZZ)/(2 sqrt(3)) has no sign-reversing similarity.
No claim is made about arbitrary rank-zero tensors in larger systems. -/
theorem scalarTensorObstruction :
    let T : Op (QAlgorithms.Qubits 2) := (-1 / (2 * Real.sqrt 3) : ℂ) • xyz 1 1 1
    T ≠ 0 ∧ ∀ (c : ℂ), c ≠ 0 → ∀ X : (Op (QAlgorithms.Qubits 2))ˣ,
      (X : Op (QAlgorithms.Qubits 2)) * (c • T) * ((X⁻¹ : (Op (QAlgorithms.Qubits 2))ˣ) : Op (QAlgorithms.Qubits 2)) ≠ -(c • T) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P95
