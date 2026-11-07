-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJPolynomialEvalHom_nonzero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJPolynomialEvalHom_nonzero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T23:42:19.33511+00:00
-- url     : https://prove2.me/theorems/642b80a6-904f-4509-b10d-258512a2ff42
-- title:
--   Tanner Lifted Product: lps Original JPolynomial Eval Hom nonzero
-- statement:
--   Nonzero polynomial gives a nonzero evaluated FUNCTION, without claiming it is nowhere zero; used by the root fixture.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L130-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L130-L135

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJPolynomialEvalHom_nonzero (P : Polynomial ℂ) (hP : P≠0) :
    lpsOriginalJPolynomialEvalHom P≠0 := by sorry
