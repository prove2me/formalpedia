-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicCovectorPullback_filled
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicCovectorPullback_filled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:06:51.259369+00:00
-- url     : https://prove2.me/theorems/ba1ec014-6396-46f8-a781-ec95dbb38568
-- title:
--   Tanner Lifted Product: lps Original Holomorphic Covector Pullback filled
-- statement:
--   Pulling back the filled differential of an original cusp form recovers its coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicDifferentialComparison.lean#L80-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicDifferentialComparison.lean#L80-L93

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicDifferentialComparison
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicCovectorPullback_filled
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsOriginalHolomorphicCovectorPullback N hN
      (lpsOriginalFilledHolomorphicDifferential N hN f) = f := by sorry
