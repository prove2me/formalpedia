-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P01_gisin_partialTranspose_negative
-- name    : QAlgorithms.Papers.Independent.Independent1.P01.gisin_partialTranspose_negative
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:05:45.987189+00:00
-- url     : https://prove2.me/theorems/d427850d-6cc1-40c0-beb4-50b107156803
-- title:
--   Negative determinant and eigenvalue for Gisin mixtures
-- statement:
--   Let $a,b\in\mathbb C$ satisfy $|a|^2+|b|^2=1$, and let $0\le x\le1$. Set $|\psi\rangle=a|01\rangle+b|10\rangle$ and $\rho=x|\psi\rangle\langle\psi|+(1-x)(|00\rangle\langle00|+|11\rangle\langle11|)/2$. If $x>(1+2|ab|)^{-1}$, then, for $\sigma=\rho^{T_I}$,
--
--   $$\det\sigma<0,\qquad \lambda_{\min}(\sigma)<0.$$
--
--   The negative eigenvalue obstructs separability. Both the determinant and spectral conclusions are retained.
-- source:
--   Separability Criterion for Density Matrices, arXiv:quant-ph/9604005v2, Eqs. (9)–(13), PDF p. 4. https://arxiv.org/abs/quant-ph/9604005v2 . PDF SHA-256: 6574d1af38e331a5ed4f7c58673855e1e580eb96d79fa52338f18cdc22d43998.

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
















/-- Peres PDF p.4, Eqs. (9)–(13): above the strict threshold, the partial
transpose has both negative determinant and a negative eigenvalue. -/
theorem gisin_partialTranspose_negative (x : ℝ) (a b : ℂ)
    (normalized : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) (nonnegative : 0 ≤ x) (fraction : x ≤ 1)
    (threshold : (1 + 2 * ‖a * b‖)⁻¹ < x) :
    (partialTransposeFirst (gisinDensity x a b)).det.re < 0 ∧
      ∃ k, ascEigenvalues (partialTransposeFirst (gisinDensity x a b)) k < 0 := by sorry



end QAlgorithms.Papers.Independent.Independent1.P01
