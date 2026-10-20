-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_qubit_bracketWitness
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.qubit_bracketWitness
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:46:38.476757+00:00
-- url     : https://prove2.me/theorems/53d4ef85-c54b-4f08-a1a8-7d5d92d1782b
-- title:
--   Remark 2.18: qubit bracket-closure witness
-- statement:
--   For a positive integer \(d\), operators act on \(\mathbb C^d\). The real ambient LK algebra consists of complex-linear, Hermiticity-preserving, trace-annihilating superoperators, with the composition commutator as bracket. In a Hilbert--Schmidt orthonormal traceless Hermitian basis \(F_j\), physical generators have the GKLS form with Hamiltonian term \(-i[H,\rho]\), half anticommutator, and positive semidefinite Kossakowski matrix \(K\). Write \(W_{\rm GKLS}\) for this cone and call a generator purely Hamiltonian when it equals \(-i[H,\cdot]\) for a traceless Hermitian \(H\).
--
--   For a qubit, take \(\sigma_-=|1\rangle\langle0|\), the usual Pauli matrix \(\sigma_x\), and write \(D_L(\rho)=L\rho L^\dagger-\{L^\dagger L,\rho\}/2\). Then
--   \[
--   B=[D_{\sigma_-},D_{\sigma_x}]
--   \]
--   is a nonzero pure Bloch translation: its linear part is zero and its translation is \((0,0,-2)\). In the normalized Pauli basis its Kossakowski characteristic polynomial is \(z(z-1)(z+1)\). Thus its spectrum is \(\{-1,0,1\}\), and it is not physical although both input dissipators are physical.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 13, Remark 2.18: qubit bracket-closure witness

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

/-- arXiv:2608.27330v1, PDF p.13, Remark 2.18, explicit qubit witness.
The characteristic polynomial records all three normalized Kossakowski eigenvalues. -/
theorem qubit_bracketWitness :
    P59.IsPhysicalAction pauliBasis (P26.applyMap (dissipatorMap sigmaMinus)) ∧
    P59.IsPhysicalAction pauliBasis (P26.applyMap (dissipatorMap (sigma 0))) ∧
    (let B := ⁅dissipatorMap sigmaMinus, dissipatorMap (sigma 0)⁆
     B ≠ 0 ∧ blochQ B = 0 ∧ blochB B = ![0, 0, -2] ∧
     (pauliKossakowskiMatrix B).charpoly = Polynomial.X * (Polynomial.X - 1) * (Polynomial.X + 1) ∧
     ¬ P59.IsPhysicalAction pauliBasis (P26.applyMap B)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
