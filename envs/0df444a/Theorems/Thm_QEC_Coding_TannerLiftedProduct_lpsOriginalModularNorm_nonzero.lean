-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularNorm_nonzero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalModularNorm_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:52:37.519294+00:00
-- url     : https://prove2.me/theorems/20c6be44-23d9-4a10-8cdd-f2d1e6e7e95a
-- title:
--   Tanner Lifted Product: lps Original Modular Norm nonzero
-- statement:
--   Genuine original input norm is a nonzero modular form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L121-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L121-L123

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalModularNorm_nonzero (N : ℕ) [NeZero N] (hN : 0<N) (c : ℂ) :
    lpsOriginalModularNorm N hN c≠0 := by sorry
