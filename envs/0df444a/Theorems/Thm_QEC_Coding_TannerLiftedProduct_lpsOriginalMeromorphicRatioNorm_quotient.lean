-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioNorm_quotient
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicRatioNorm_quotient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:37:10.355174+00:00
-- url     : https://prove2.me/theorems/8ec7c482-6033-4dc6-9ef8-2d0cbf4937aa
-- title:
--   Tanner Lifted Product: lps Original Meromorphic Ratio Norm quotient
-- statement:
--   Actual quotient-function linearity for the same-weight input A-cB.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L38-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L38-L50

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicRatioNorm_quotient
    (N : ℕ) (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k) (c : ℂ)
    (q : LPSOriginalMeromorphicCosets N) (τ : ℍ) :
    SlashInvariantForm.quotientFunc (A-c • B) q τ =
      SlashInvariantForm.quotientFunc A q τ - c * SlashInvariantForm.quotientFunc B q τ := by sorry
