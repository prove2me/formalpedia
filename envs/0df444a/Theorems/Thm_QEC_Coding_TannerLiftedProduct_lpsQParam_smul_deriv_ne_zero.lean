-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQParam_smul_deriv_ne_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsQParam_smul_deriv_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:43:02.429814+00:00
-- url     : https://prove2.me/theorems/fab5207f-7ab1-4795-bfbd-652f776fdd5b
-- title:
--   Tanner Lifted Product: lps QParam smul deriv ne zero
-- statement:
--   At nonzero width, the actual q and Mobius derivative formulas give a nonzero composed derivative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspAnalytic.lean#L29-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspAnalytic.lean#L29-L41

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferentialCharts
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspAnalytic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsQParam_smul_deriv_ne_zero (h : ℝ) (hh : h≠0) (g : GL (Fin 2) ℝ)
    (hg : 0<g.val.det) (τ : ℍ) :
    deriv (fun z : ℂ => Function.Periodic.qParam h ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) τ≠0 := by sorry
