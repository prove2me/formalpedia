-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_cusp_cusp_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_cusp_cusp_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:01:29.268731+00:00
-- url     : https://prove2.me/theorems/005dd7ce-1f0e-476a-b9d4-b58b22e66825
-- title:
--   Tanner Lifted Product: lps Original Filled cusp cusp analytic
-- statement:
--   Distinct actual cusp chart sources are disjoint; the same selected cusp gives a locally identity analytic transition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledAnalytic.lean#L86-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledAnalytic.lean#L86-L106

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_cusp_cusp_analytic (N : ℕ) [NeZero N]
    (c d : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (z : ℂ) (hz : letI := lpsOriginalFilledTopology N
      z∈((lpsOriginalFilledCuspChart N c).symm.trans
        (lpsOriginalFilledCuspChart N d)).source) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ ((lpsOriginalFilledCuspChart N c).symm.trans
      (lpsOriginalFilledCuspChart N d)) z := by sorry
