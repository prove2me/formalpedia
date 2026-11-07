-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_comp_const_mul
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalTaylorSeries_comp_const_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:07:59.728195+00:00
-- url     : https://prove2.me/theorems/f41f78be-2fc8-4290-bce9-01c47b27d97c
-- title:
--   Tanner Lifted Product: lps Original Taylor Series comp const mul
-- statement:
--   Actual analytic Taylor expansion respects constant rescaling.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L383-L406
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L383-L406

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalTaylorSeries_comp_const_mul
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (c : ℂ) :
    lpsOriginalTaylorSeries (fun q => f (c*q)) =
      PowerSeries.rescale c (lpsOriginalTaylorSeries f) := by sorry
