-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJDilated_cusp_param
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJDilated_cusp_param
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:19:14.621768+00:00
-- url     : https://prove2.me/theorems/1e4d1ce6-29d5-465f-97ed-3e220c87ded2
-- title:
--   Tanner Lifted Product: lps Original Filled JDilated cusp param
-- statement:
--   Every actual nonzero full-disc parameter recovers the genuine minimum-width translated cusp coefficient; used by the literal punctured chart germ.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L296-L307
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L296-L307

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJDilated_cusp_param (N : ℕ) [NeZero N] (hN : 0<N)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
    (hq0 : q.val≠0) :
    lpsOriginalFilledJDilated N hN (lpsOriginalFilledCuspParam N c q)=
      lpsOriginalJDilationCuspCoefficient N hN (lpsOriginalCuspRepresentative N c) q.val := by sorry
