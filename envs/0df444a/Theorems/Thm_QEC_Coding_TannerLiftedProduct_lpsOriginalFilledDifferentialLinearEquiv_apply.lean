-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledDifferentialLinearEquiv_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledDifferentialLinearEquiv_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:05:51.863051+00:00
-- url     : https://prove2.me/theorems/a7b71b66-bf79-4f20-b802-c9c0a161c87d
-- title:
--   Tanner Lifted Product: lps Original Filled Differential Linear Equiv apply
-- statement:
--   The forward equivalence is the genuine previously constructed filled differential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicDifferentialComparison.lean#L872-L876
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicDifferentialComparison.lean#L872-L876

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicDifferentialComparison
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledDifferentialLinearEquiv_apply
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsOriginalFilledDifferentialLinearEquiv N hN f =
      lpsOriginalFilledHolomorphicDifferential N hN f := by sorry
