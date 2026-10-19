-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P01_partialTranspose_localUnitary_spectrum
-- name    : QAlgorithms.Papers.Independent.Independent1.P01.partialTranspose_localUnitary_spectrum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:05:42.532173+00:00
-- url     : https://prove2.me/theorems/7108fff4-f3d8-4066-b521-6a3c94c71b27
-- title:
--   Local unitaries preserve the partial-transpose spectrum
-- statement:
--   Let $\rho$ be a density matrix on $\mathbb C^I\otimes\mathbb C^J$, with $I,J$ nonempty finite basis sets. Let $U$ and $V$ be arbitrary complex unitaries on the respective subsystem spaces, and set $\widetilde\rho=(U\otimes V)\rho(U\otimes V)^\dagger$. Writing $T_I$ for transposition of the first subsystem only, one has
--
--   $$\det(t\mathbf1-\widetilde\rho^{T_I})=\det(t\mathbf1-\rho^{T_I})$$
--
--   as polynomials in $t$. Hence the two partial transposes have the same eigenvalues with algebraic multiplicities. This expresses the criterion's independence of local basis choices.
-- source:
--   Separability Criterion for Density Matrices, arXiv:quant-ph/9604005v2, Prose spanning pp.2–3 and Eq. (4), PDF p. 3. https://arxiv.org/abs/quant-ph/9604005v2 . PDF SHA-256: 6574d1af38e331a5ed4f7c58673855e1e580eb96d79fa52338f18cdc22d43998.

import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P01_Model
set_option autoImplicit false

/-!
# Peres: Separability Criterion for Density Matrices

Source: arXiv:quant-ph/9604005v2, PDF pp.2–5. The first subsystem alone
is transposed, without complex conjugation. Equation (5), which has a
conjugating-factor defect, is deferred; its valid spectral conclusion is stated.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Independent1.P01

open QAlgorithms.Entanglement














/-- Peres PDF pp.2–3, prose preceding Eqs. (4)–(5): arbitrary separate local
unitaries preserve the partial-transpose spectrum, including multiplicities.
This does not assert the defective printed covariance formula (5). -/
theorem partialTranspose_localUnitary_spectrum
    {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    [DecidableEq I] [DecidableEq J]
    (rho : Matrix (I × J) (I × J) ℂ) (density : IsDensityMatrix rho)
    (U : Matrix.unitaryGroup I ℂ) (V : Matrix.unitaryGroup J ℂ) :
    (partialTransposeFirst
      (conjSuperop (Matrix.kronecker (U : Matrix I I ℂ) (V : Matrix J J ℂ)) rho)).charpoly =
      (partialTransposeFirst rho).charpoly := by sorry





end QAlgorithms.Papers.Independent.Independent1.P01
