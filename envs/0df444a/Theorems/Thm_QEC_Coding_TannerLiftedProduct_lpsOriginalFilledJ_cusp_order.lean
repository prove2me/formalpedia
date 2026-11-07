-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_cusp_order
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJ_cusp_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:24:55.512275+00:00
-- url     : https://prove2.me/theorems/0a66a300-5d06-4af3-b2a5-7f574e447361
-- title:
--   Tanner Lifted Product: lps Original Filled J cusp order
-- statement:
--   Exact order minus the positive original width at every true cusp, using actual leading coefficient1; used by the root fixture and immediate original divisor/function-field comparison.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L270-L285
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L270-L285

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJ_cusp_order (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    meromorphicOrderAt (fun q : ℂ => lpsOriginalFilledJ N
      ((lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).symm q)) 0 =
      (-(lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c):ℤ) : WithTop ℤ) := by sorry
