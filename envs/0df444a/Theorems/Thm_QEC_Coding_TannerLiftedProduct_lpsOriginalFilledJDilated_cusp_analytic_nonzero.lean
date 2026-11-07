-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJDilated_cusp_analytic_nonzero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJDilated_cusp_analytic_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:19:18.92325+00:00
-- url     : https://prove2.me/theorems/c748844a-f392-4501-a4ae-3926cf1942ad
-- title:
--   Tanner Lifted Product: lps Original Filled JDilated cusp analytic nonzero
-- statement:
--   Every nonzero actual cusp-chart target is analytic by a genuine analytic overlap with an original interior chart; used by all-chart meromorphy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L363-L391
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L363-L391

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJDilated_cusp_analytic_nonzero (N : ℕ) [NeZero N] (hpos : 0<N) (hN : 4∣N)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (z : ℂ) (hz : z∈(lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
    (hz0 : z≠0) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ (fun w : ℂ => lpsOriginalFilledJDilated N hpos
      ((lpsOriginalFilledCuspChart N c).symm w)) z := by sorry
