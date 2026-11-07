-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_cusp_germ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJ_cusp_germ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:09:20.760739+00:00
-- url     : https://prove2.me/theorems/065fe383-7b58-4051-8a2c-05079f61af34
-- title:
--   Tanner Lifted Product: lps Original Filled J cusp germ
-- statement:
--   The literal cusp chart inverse has germ K(q^width)/q^width; used by meromorphy and exact pole order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L234-L251
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L234-L251

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJ_cusp_germ (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    (fun q : ℂ => lpsOriginalFilledJ N
      ((lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).symm q)) =ᶠ[𝓝[≠] 0]
    (fun q => lpsOriginalJQCoefficient
      (q^(lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c))) /
      q^(lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c))) := by sorry
