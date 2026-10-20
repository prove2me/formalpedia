-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_twoQubit_covariance
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.twoQubit_covariance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:02:04.733598+00:00
-- url     : https://prove2.me/theorems/3d6637ba-8ff8-4b4e-a676-92921f347a81
-- title:
--   §5.1: finite dissipator covariance and the cross-superoperator
-- statement:
--   For a positive integer \(d\), operators act on \(\mathbb C^d\). The real ambient LK algebra consists of complex-linear, Hermiticity-preserving, trace-annihilating superoperators, with the composition commutator as bracket. In a Hilbert--Schmidt orthonormal traceless Hermitian basis \(F_j\), physical generators have the GKLS form with Hamiltonian term \(-i[H,\rho]\), half anticommutator, and positive semidefinite Kossakowski matrix \(K\). Write \(W_{\rm GKLS}\) for this cone and call a generator purely Hamiltonian when it equals \(-i[H,\cdot]\) for a traceless Hermitian \(H\).
--
--   For two qubits, set \(H=\sigma_{A,x}\otimes I_B/2\), \(J_0=|0\rangle\langle0|_A\otimes|1\rangle\langle0|_B\), and \(U_t=e^{-itH}\). For every jump \(L\) and real \(t\),
--   \[
--   e^{t\operatorname{ad}L_H}D_L=D_{U_tLU_t^\dagger}.
--   \]
--   With \(M=-i[H,J_0]=-\sigma_{A,y}\otimes\sigma_{B,-}/2\), the bracket \([L_H,D_{J_0}]\) is the cross-superoperator
--   \(X\mapsto MXJ_0^\dagger+J_0XM^\dagger-\{M^\dagger J_0+J_0^\dagger M,X\}/2\).
--   At \(t=\pi/2\), the orbit jump is \((I-\sigma_y)_A\otimes\sigma_{B,-}/2\). This retains the full projector and does not replace the bilinear cross term by \(D_M\).
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 33, §5.1: finite dissipator covariance and the cross-superoperator

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P12

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.Frobenius

open Set

namespace QAlgorithms.Papers.Independent.Dependency50.P12

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] Classical.propDecidable Classical.decEq

open Coordinates

open QAlgorithms.Papers.Independent.Information100

attribute [local instance] QAlgorithms.Papers.Independent.Dependency50.P12.inheritedSubalgebraTopologicalAddGroup

/-- arXiv:2608.27330v1, PDF p.33, Equations (52)--(53), including the finite orbit.
The derivative is the cross-superoperator, not D_M; the finite jump retains P_yminus. -/
theorem twoQubit_covariance :
    (∀ (t : ℝ) (L : P59.Operator 4),
      let U := NormedSpace.exp ((-Complex.I * (t : ℂ)) • twoQubitH 0)
      expAd (t • coherentMap (twoQubitH 0)) (dissipatorMap L) = dissipatorMap (U * L * Uᴴ)) ∧
    P59.coherent (twoQubitH 0) modulatedJ0 =
      (-(1/2 : ℂ)) • tensor2 (sigma 1) sigmaMinus ∧
    ⁅coherentMap (twoQubitH 0), dissipatorMap modulatedJ0⁆ =
      crossSuper modulatedJ0 (P59.coherent (twoQubitH 0) modulatedJ0) ∧
    (let U := NormedSpace.exp ((-Complex.I * ((Real.pi/2 : ℝ) : ℂ)) • twoQubitH 0)
     U * modulatedJ0 * Uᴴ = tensor2 ((2⁻¹ : ℂ) • (1 - sigma 1)) sigmaMinus) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
