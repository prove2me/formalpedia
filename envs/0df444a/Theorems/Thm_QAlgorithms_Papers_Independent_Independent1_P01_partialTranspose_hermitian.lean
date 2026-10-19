-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P01_partialTranspose_hermitian
-- name    : QAlgorithms.Papers.Independent.Independent1.P01.partialTranspose_hermitian
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:05:41.850145+00:00
-- url     : https://prove2.me/theorems/6ea52ff8-1ffc-462f-a79c-aaf40f4ff260
-- title:
--   Partial transposition preserves Hermiticity
-- statement:
--   Let $\rho$ be a density matrix on two nonempty finite subsystem spaces with basis sets $I$ and $J$. Define $\sigma_{m\mu,n\nu}=\rho_{n\mu,m\nu}$, transposing only the first subsystem. Then
--
--   $$\sigma^\dagger=\sigma.$$
--
--   The assertion holds for arbitrary subsystem dimensions and requires no separable decomposition. It makes the eigenvalue test a test on a Hermitian matrix.
-- source:
--   Separability Criterion for Density Matrices, arXiv:quant-ph/9604005v2, Paragraph after Eq. (3), PDF p. 2. https://arxiv.org/abs/quant-ph/9604005v2 . PDF SHA-256: 6574d1af38e331a5ed4f7c58673855e1e580eb96d79fa52338f18cdc22d43998.

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













/-- Peres PDF p.2, paragraph after Eq. (3): the partial transpose of a density
matrix is Hermitian, without assuming separability. -/
theorem partialTranspose_hermitian
    {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    [DecidableEq I] [DecidableEq J]
    (rho : Matrix (I × J) (I × J) ℂ) (density : IsDensityMatrix rho) :
    (partialTransposeFirst rho).IsHermitian := by sorry






end QAlgorithms.Papers.Independent.Independent1.P01
