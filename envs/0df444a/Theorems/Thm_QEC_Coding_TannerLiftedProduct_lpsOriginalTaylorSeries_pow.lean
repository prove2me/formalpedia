-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_pow
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalTaylorSeries_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:06:34.406097+00:00
-- url     : https://prove2.me/theorems/21652208-7b80-4117-821b-10ac3bea8564
-- title:
--   Tanner Lifted Product: lps Original Taylor Series pow
-- statement:
--   Actual analytic power Taylor identity by genuine product closure and induction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalQExpansionArithmetic.lean#L74-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalQExpansionArithmetic.lean#L74-L78

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.RingTheory.PowerSeries.Inverse
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology UpperHalfPlane ModularForm MatrixGroups
open scoped UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalTaylorSeries_pow {f : ℂ→ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    lpsOriginalTaylorSeries (f^n)=(lpsOriginalTaylorSeries f)^n := by sorry
