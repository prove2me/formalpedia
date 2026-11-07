-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicPullback_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicPullback_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T01:20:55.390958+00:00
-- url     : https://prove2.me/theorems/d3ab1d5d-dbd2-47a7-9d80-c64771586a00
-- title:
--   Tanner Lifted Product: lps Original Holomorphic Pullback apply
-- statement:
--   Literal pointwise identity of the actual holomorphic pullback; exercised by the genuine root API example.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactFunctionFieldDegree.lean#L46-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactFunctionFieldDegree.lean#L46-L48

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicPullback_apply (g : 𝒮ℒ)
    (f : LPSOriginalHolomorphicRing) (τ : ℍ) :
    (lpsOriginalHolomorphicPullback g f).val τ=f.val (g.val⁻¹•τ) := by sorry
