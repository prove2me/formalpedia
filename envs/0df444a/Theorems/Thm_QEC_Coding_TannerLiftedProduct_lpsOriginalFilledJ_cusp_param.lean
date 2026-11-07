-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_cusp_param
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJ_cusp_param
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:09:16.657268+00:00
-- url     : https://prove2.me/theorems/b564ee2f-60f3-41dc-8a11-9ed21a83d609
-- title:
--   Tanner Lifted Product: lps Original Filled J cusp param
-- statement:
--   Every actual nonzero filled-disc parameter satisfies q^width*j=K(q^width); used by the original cusp germ.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L208-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L208-L230

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJ_cusp_param (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
    (hq0 : q.val≠0) :
    q.val^(lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c)) *
      lpsOriginalFilledJ N (lpsOriginalFilledCuspParam N c q)=
      lpsOriginalJQCoefficient
        (q.val^(lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c))) := by sorry
