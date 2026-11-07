-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJDilated_cusp_germ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJDilated_cusp_germ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:19:18.007208+00:00
-- url     : https://prove2.me/theorems/8adbd1aa-141a-4095-bfe8-c26a7c7b8626
-- title:
--   Tanner Lifted Product: lps Original Filled JDilated cusp germ
-- statement:
--   The actual added-cusp inverse has precisely the translated-ratio punctured germ; used by cusp meromorphy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L310-L322
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L310-L322

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJDilated_cusp_germ (N : ℕ) [NeZero N] (hN : 0<N)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    (fun q : ℂ => lpsOriginalFilledJDilated N hN
      ((lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).symm q)) =ᶠ[𝓝[≠] 0]
      lpsOriginalJDilationCuspCoefficient N hN (lpsOriginalCuspRepresentative N c) := by sorry
