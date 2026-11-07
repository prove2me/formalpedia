-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularNormInput_nonzero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalModularNormInput_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:55:29.782034+00:00
-- url     : https://prove2.me/theorems/b4cf94ee-f814-4761-886c-b6e100d380be
-- title:
--   Tanner Lifted Product: lps Original Modular Norm Input nonzero
-- statement:
--   Actual original norm input is a nonzero function by proved jN nonconstancy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L103-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L103-L112

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalModularNormInput_nonzero (N : ℕ) (hN : 0<N) (c : ℂ) :
    (lpsOriginalModularNormInput N hN c:ℍ→ℂ)≠0 := by sorry
