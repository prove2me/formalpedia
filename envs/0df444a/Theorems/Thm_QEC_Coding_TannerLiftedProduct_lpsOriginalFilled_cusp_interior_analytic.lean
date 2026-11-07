-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_cusp_interior_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_cusp_interior_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:59:08.442172+00:00
-- url     : https://prove2.me/theorems/32a08ae6-ab5d-428e-a3bf-d0569cfee94b
-- title:
--   Tanner Lifted Product: lps Original Filled cusp interior analytic
-- statement:
--   The real reverse mixed transition is analytic by the actual inverse-function theorem and chart inverse laws.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledAnalytic.lean#L66-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledAnalytic.lean#L66-L83

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_cusp_interior_analytic (N : ℕ) [NeZero N] (hN : 4∣N)
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (z : ℂ) (hz : letI := lpsOriginalFilledTopology N
      z∈((lpsOriginalFilledCuspChart N c).symm.trans
        (lpsOriginalFilledInteriorChart N hN x)).source) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ ((lpsOriginalFilledCuspChart N c).symm.trans
      (lpsOriginalFilledInteriorChart N hN x)) z := by sorry
