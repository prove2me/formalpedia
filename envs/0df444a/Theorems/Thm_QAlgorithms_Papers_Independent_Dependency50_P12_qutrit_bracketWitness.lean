-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_qutrit_bracketWitness
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.qutrit_bracketWitness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:42:26.808454+00:00
-- url     : https://prove2.me/theorems/9004d8b7-e717-4941-ac48-6d646e5bae53
-- title:
--   Example 1.1 and Appendix A.4: explicit qutrit failure of bracket closure
-- statement:
--   For a positive integer \(d\), operators act on \(\mathbb C^d\). The real ambient LK algebra consists of complex-linear, Hermiticity-preserving, trace-annihilating superoperators, with the composition commutator as bracket. In a Hilbert--Schmidt orthonormal traceless Hermitian basis \(F_j\), physical generators have the GKLS form with Hamiltonian term \(-i[H,\rho]\), half anticommutator, and positive semidefinite Kossakowski matrix \(K\). Write \(W_{\rm GKLS}\) for this cone and call a generator purely Hamiltonian when it equals \(-i[H,\cdot]\) for a traceless Hermitian \(H\).
--
--   For a qutrit, use the standard raw Gell--Mann matrices \(\lambda_j\), normalized by \(\operatorname{Tr}(\lambda_j\lambda_k)=2\delta_{jk}\), and set \(L_1=\lambda_1+i\lambda_4\), \(L_2=\lambda_2+i\lambda_5\). Each \(D_{L_i}\) is a valid single-jump dissipator. For \(B=[D_{L_1},D_{L_2}]\), use the unnormalized output-first Choi matrix and orthogonally compress away from \(\sum_i|ii\rangle\). Its full nine-dimensional conditional compression is Hermitian and has characteristic polynomial
--   \[
--   z^7(z-4)(z+4).
--   \]
--   In particular it has a nonzero eigenvector of eigenvalue \(-4\), fails conditional complete positivity, and lies outside \(W_{\rm GKLS}\). The kernel, including the maximally entangled direction, is retained explicitly.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 3, Example 1.1 and Appendix A.4: explicit qutrit failure of bracket closure

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

/-- arXiv:2608.27330v1, PDF pp.3,44--45, Example 1.1 and Appendix A.4.
The full nine-dimensional compression has seven zero eigenvalues; the eighth
traceless dimension of K and the maximally entangled kernel are not conflated. -/
theorem qutrit_bracketWitness :
    P59.IsPhysicalAction gellMannBasis (P26.applyMap (dissipatorMap qutritJump1)) ∧
    P59.IsPhysicalAction gellMannBasis (P26.applyMap (dissipatorMap qutritJump2)) ∧
    (let B := ⁅dissipatorMap qutritJump1, dissipatorMap qutritJump2⁆
     (compressedGeneratorChoi B).IsHermitian ∧
     (compressedGeneratorChoi B).charpoly = Polynomial.X ^ 7 *
       (Polynomial.X - Polynomial.C (4 : ℂ)) * (Polynomial.X + Polynomial.C (4 : ℂ)) ∧
     (∃ v : (Fin 3 × Fin 3) → ℂ, v ≠ 0 ∧
       (compressedGeneratorChoi B).mulVec v = (-4 : ℂ) • v) ∧
     ¬ (compressedGeneratorChoi B).PosSemidef ∧ ¬ P59.IsPhysicalAction gellMannBasis (P26.applyMap B)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
