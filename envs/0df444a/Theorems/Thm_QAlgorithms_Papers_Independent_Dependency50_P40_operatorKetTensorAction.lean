-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P40_operatorKetTensorAction
-- name    : QAlgorithms.Papers.Independent.Dependency50.P40.operatorKetTensorAction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:18:12.041934+00:00
-- url     : https://prove2.me/theorems/52cd35e8-774d-499b-91dd-ff6fa0610bac
-- title:
--   Tensor action on an unnormalized operator ket
-- statement:
--   Take positive dimensions $h_1,h_2,k_1,k_2$, and arbitrary complex matrices $A:\mathbb C^{h_1}\to\mathbb C^{k_1}$, $B:\mathbb C^{h_2}\to\mathbb C^{k_2}$ and $C:\mathbb C^{h_2}\to\mathbb C^{h_1}$. Define $|C\rangle\rangle=\sum_{x,y}C_{xy}|x\rangle|y\rangle$ with no normalization. Then
--
--   $$
--   (A\otimes B)|C\rangle\rangle=|ACB^T\rangle\rangle.
--   $$
--
--   Here $T$ is transpose in the fixed bases without conjugation. This identity transports matrix multiplication to the output–input tensor representation; the matrices need not be unitary or normalized.
-- source:
--   Optimum Quantum Error Recovery using Semidefinite Programming, arXiv:quant-ph/0606035v1, PDF p. 3, III, Eq. (11): tensor action on an operator ket

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P40

open scoped ComplexConjugate ComplexOrder Matrix

open QAlgorithms.Papers.Independent.Information100.P34 (dyad)

/-- PDF p.3, (11): the second tensor factor gives a transpose, not an adjoint. -/
theorem operatorKetTensorAction {h1 h2 k1 k2 : ℕ}
    (hh1 : 0 < h1) (hh2 : 0 < h2) (hk1 : 0 < k1) (hk2 : 0 < k2)
    (A : Matrix (Fin k1) (Fin h1) ℂ) (B : Matrix (Fin k2) (Fin h2) ℂ)
    (C : Matrix (Fin h1) (Fin h2) ℂ) :
    matrixAction (Matrix.kronecker A B) (operatorKet C) = operatorKet (A * C * Bᵀ) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P40

end
