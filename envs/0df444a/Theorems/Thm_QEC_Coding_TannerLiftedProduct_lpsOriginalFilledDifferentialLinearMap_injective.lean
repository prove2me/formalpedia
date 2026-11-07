-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledDifferentialLinearMap_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledDifferentialLinearMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:09:28.148703+00:00
-- url     : https://prove2.me/theorems/3ff1c0b3-29b2-4568-b50e-8063dbee3456
-- title:
--   Tanner Lifted Product: lps Original Filled Differential Linear Map injective
-- statement:
--   The original cusp-form map into analytic covector sections is injective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledDifferential.lean#L301-L311
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledDifferential.lean#L301-L311

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialGluing
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledDifferential
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledDifferentialLinearMap_injective (N : ℕ) [NeZero N] (hN : 4∣N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    Function.Injective (lpsOriginalFilledDifferentialLinearMap N hN) := by sorry
