-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch8_perspective_sqrt_normalization
-- name    : TroppMatrixConcentration.ch8_perspective_sqrt_normalization
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T14:47:18.99589+00:00
-- url     : https://prove2.me/theorems/7e364931-1b7d-45fd-9ddb-2bde4a82ce6c
-- title:
--   Square-root and inverse-square-root identities for positive definite matrices
-- statement:
--   Let $A$ be a finite-dimensional positive definite complex matrix, and define its square root and inverse square root by spectral functional calculus:
--   $$S=\sqrt A,\qquad R=A^{-1/2}.$$
--   Both are Hermitian, and
--   $$S^2=A,\qquad RS=SR=I.$$
-- source:
--   Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1, Definition 8.6.1 and proof of Theorem 8.6.2, printed pp. 134–135 (PDF pp. 140–141), positive-definite square-root normalization.

import Definitions.Def_TroppMatrixConcentration_ch8_entropy

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TroppMatrixConcentration

theorem ch8_perspective_sqrt_normalization
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) (hA : A.PosDef) :
    let S := ch8_matrixFunction Real.sqrt A
    let R := ch8_matrixFunction (fun x => (Real.sqrt x)⁻¹) A
    S.IsHermitian ∧ R.IsHermitian ∧ S * S = A ∧ R * S = 1 ∧ S * R = 1 := by sorry

end TroppMatrixConcentration
