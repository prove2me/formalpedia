-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJPolynomialEvalHom_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJPolynomialEvalHom_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:34:55.01261+00:00
-- url     : https://prove2.me/theorems/8e0fb126-f030-4687-b722-7913eb0c5324
-- title:
--   Tanner Lifted Product: lps Original JPolynomial Eval Hom injective
-- statement:
--   Equality on the actual infinite original j image proves polynomial equality; used by nonzero-function control and uniqueness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L121-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L121-L127

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Separation.Connected
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJPolynomialEvalHom_injective :
    Function.Injective lpsOriginalJPolynomialEvalHom := by sorry
