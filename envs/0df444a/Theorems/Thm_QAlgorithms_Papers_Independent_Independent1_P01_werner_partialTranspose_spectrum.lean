-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P01_werner_partialTranspose_spectrum
-- name    : QAlgorithms.Papers.Independent.Independent1.P01.werner_partialTranspose_spectrum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:05:49.429807+00:00
-- url     : https://prove2.me/theorems/d9f2dd0e-d0a0-4ca8-8a23-9ae512a69385
-- title:
--   Impure-singlet partial-transpose spectrum
-- statement:
--   For two qubits, let $|s\rangle=(|01\rangle-|10\rangle)/\sqrt2$, $S=|s\rangle\langle s|$, and $\rho_x=xS+(1-x)\mathbf1_4/4$, where $0\le x\le1$. Let $\sigma_x=\rho_x^{T_I}$. Its characteristic polynomial is
--
--   $$\det(t\mathbf1_4-\sigma_x)=\left(t-\frac{1-3x}{4}\right)\left(t-\frac{1+x}{4}\right)^3.$$
--
--   In particular, if $x<1/3$, then $\sigma_x$ is positive definite and satisfies the necessary separability criterion. The calculation identifies the effect of white noise, whose random fraction includes all four Bell components equally.
-- source:
--   Separability Criterion for Density Matrices, arXiv:quant-ph/9604005v2, Eqs. (7)–(8) and following calculation, PDF p. 3. https://arxiv.org/abs/quant-ph/9604005v2 . PDF SHA-256: 6574d1af38e331a5ed4f7c58673855e1e580eb96d79fa52338f18cdc22d43998.

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















/-- Peres PDF p.3, Eqs. (7)–(8): the impure singlet has partial-transpose
eigenvalues `(1+x)/4` three times and `(1-3x)/4` once. For `x < 1/3`
the matrix is positive definite (hence satisfies the necessary criterion). -/
theorem werner_partialTranspose_spectrum (x : ℝ) (nonnegative : 0 ≤ x) (fraction : x ≤ 1) :
    (partialTransposeFirst (wernerDensity x)).charpoly =
      (Polynomial.X - Polynomial.C (((1 - 3 * x) / 4 : ℝ) : ℂ)) *
        (Polynomial.X - Polynomial.C (((1 + x) / 4 : ℝ) : ℂ)) ^ 3 ∧
    (x < 1 / 3 → (partialTransposeFirst (wernerDensity x)).PosDef) := by sorry




end QAlgorithms.Papers.Independent.Independent1.P01
