-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJPolynomialEvalHom_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJPolynomialEvalHom_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:35:07.057065+00:00
-- url     : https://prove2.me/theorems/b31e7db6-1d1b-4bd2-91b3-6be274abe5b2
-- title:
--   Tanner Lifted Product: lps Original JPolynomial Eval Hom apply
-- statement:
--   Literal actual ring-hom evaluation formula; used by the root fixture.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L117-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean#L117-L118

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJPolynomialEvalHom_apply (P : Polynomial ℂ) (τ : ℍ) :
    lpsOriginalJPolynomialEvalHom P τ=P.eval (lpsOriginalJInvariant τ) := by sorry
