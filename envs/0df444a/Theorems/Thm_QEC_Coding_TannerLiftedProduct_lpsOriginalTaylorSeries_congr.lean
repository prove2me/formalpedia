-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_congr
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalTaylorSeries_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:21:19.884971+00:00
-- url     : https://prove2.me/theorems/db24015f-49d6-4632-8d82-9037908194db
-- title:
--   Tanner Lifted Product: lps Original Taylor Series congr
-- statement:
--   Actual neighborhood-germ equality gives identical Taylor coefficients by derivative locality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalQExpansionArithmetic.lean#L43-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalQExpansionArithmetic.lean#L43-L47

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalTaylorSeries_congr {f g : ℂ→ℂ} (h : f=ᶠ[𝓝 0]g) :
    lpsOriginalTaylorSeries f=lpsOriginalTaylorSeries g := by sorry
