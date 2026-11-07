-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_mul
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalTaylorSeries_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:04:31.993044+00:00
-- url     : https://prove2.me/theorems/49895c13-532c-4f3e-be24-dfbb581cf572
-- title:
--   Tanner Lifted Product: lps Original Taylor Series mul
-- statement:
--   Actual analytic product Taylor identity proved from iterated derivative multiplication and factorials.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalQExpansionArithmetic.lean#L50-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalQExpansionArithmetic.lean#L50-L60

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalTaylorSeries_mul {f g : ℂ→ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    lpsOriginalTaylorSeries (f*g)=
      lpsOriginalTaylorSeries f*lpsOriginalTaylorSeries g := by sorry
