-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_cusp_meromorphic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJ_cusp_meromorphic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:08:52.587939+00:00
-- url     : https://prove2.me/theorems/3e3cdf1a-c2ae-4d1d-9b39-5a3f9d5be24d
-- title:
--   Tanner Lifted Product: lps Original Filled J cusp meromorphic
-- statement:
--   Meromorphy at each actual added cusp under the true minimum-width chart; used by pole order and all-chart meromorphy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L254-L267
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L254-L267

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJ_cusp_meromorphic (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    MeromorphicAt (fun q : ℂ => lpsOriginalFilledJ N
      ((lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).symm q)) 0 := by sorry
