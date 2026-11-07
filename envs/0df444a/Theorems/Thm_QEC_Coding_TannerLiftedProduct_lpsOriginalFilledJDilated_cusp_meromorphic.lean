-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJDilated_cusp_meromorphic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJDilated_cusp_meromorphic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:19:14.666209+00:00
-- url     : https://prove2.me/theorems/1bf9ca4f-fd02-457a-a9fd-9facb88337be
-- title:
--   Tanner Lifted Product: lps Original Filled JDilated cusp meromorphic
-- statement:
--   Meromorphy at every genuine added cusp in the actual original minimum-width chart; used by all-chart meromorphy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L325-L330
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L325-L330

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJDilated_cusp_meromorphic (N : ℕ) [NeZero N] (hN : 0<N)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    MeromorphicAt (fun q : ℂ => lpsOriginalFilledJDilated N hN
      ((lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).symm q)) 0 := by sorry
