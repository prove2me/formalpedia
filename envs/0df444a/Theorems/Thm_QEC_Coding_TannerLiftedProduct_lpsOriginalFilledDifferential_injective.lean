-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledDifferential_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledDifferential_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:08:25.486135+00:00
-- url     : https://prove2.me/theorems/60c1cb75-333f-443b-9f9a-e5295391e924
-- title:
--   Tanner Lifted Product: lps Original Filled Differential injective
-- statement:
--   The intrinsic global differential faithfully determines the original cusp form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledDifferential.lean#L195-L207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledDifferential.lean#L195-L207

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialGluing
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledDifferential
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledDifferential_injective (N : ℕ) [NeZero N] (hN : 4∣N) :
    Function.Injective (lpsOriginalFilledDifferential N hN) := by sorry
