-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJDilated_interior_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJDilated_interior_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:16:18.647194+00:00
-- url     : https://prove2.me/theorems/c924e09f-71aa-4350-b3f7-98c75d4b19cf
-- title:
--   Tanner Lifted Product: lps Original Filled JDilated interior analytic
-- statement:
--   Analyticity at every target point of every true original interior chart; used by nonzero cusp overlaps and all-chart meromorphy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L344-L359
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L344-L359

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJDilated_interior_analytic (N : ℕ) [NeZero N] (hpos : 0<N) (hN : 4∣N)
    (x : MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (z : ℂ) (hz : z∈(lpsOriginalFilledInteriorChart N hN x).target) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ (fun w : ℂ => lpsOriginalFilledJDilated N hpos
      ((lpsOriginalFilledInteriorChart N hN x).symm w)) z := by sorry
