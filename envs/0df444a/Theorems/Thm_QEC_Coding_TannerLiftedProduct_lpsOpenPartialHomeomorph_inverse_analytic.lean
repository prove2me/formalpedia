-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOpenPartialHomeomorph_inverse_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOpenPartialHomeomorph_inverse_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:00:58.824989+00:00
-- url     : https://prove2.me/theorems/09c31049-5842-4aee-a974-f19a75a1a8d7
-- title:
--   Tanner Lifted Product: lps Open Partial Homeomorph inverse analytic
-- statement:
--   A true complex partial homeomorphism with analytic nonzero derivative has an analytic inverse by its actual inverse laws.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledAnalytic.lean#L19-L27
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledAnalytic.lean#L19-L27

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspAnalytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOpenPartialHomeomorph_inverse_analytic
    (e : OpenPartialHomeomorph ℂ ℂ) (z : ℂ) (hz : z∈e.source)
    (ha : AnalyticAt ℂ e z) (hd : deriv e z≠0) :
    AnalyticAt ℂ e.symm (e z) := by sorry
