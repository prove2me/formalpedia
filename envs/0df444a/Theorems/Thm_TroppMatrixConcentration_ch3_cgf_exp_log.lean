-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch3_cgf_exp_log
-- name    : TroppMatrixConcentration.ch3_cgf_exp_log
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T14:20:27.452985+00:00
-- url     : https://prove2.me/theorems/ff43e744-9cc6-47a6-a13c-e3c597930055
-- title:
--   Hermitian exponential is positive definite and logarithm is its inverse
-- statement:
--   For every finite-dimensional complex Hermitian matrix $A$,
--
--   $$e^A\succ0,\qquad\log(e^A)=A.$$
--
--   The exponential is the normed-algebra matrix exponential and the logarithm uses real spectral functional calculus. Dimension zero is allowed. These identities connect random Hermitian matrices with the positive-definite domain of Lieb’s theorem.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015), https://arxiv.org/abs/1501.01571v1; Sections 2.1.11–12, especially equation (2.1.17), printed pp. 22–23; used in Corollary 3.4.2, printed p. 35.

import Definitions.Def_TroppMatrixConcentration_spectral

open scoped Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace TroppMatrixConcentration

theorem ch3_cgf_exp_log {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) :
    (matrixExp A).PosDef ∧ matrixLog (matrixExp A) = A := by sorry

end TroppMatrixConcentration
