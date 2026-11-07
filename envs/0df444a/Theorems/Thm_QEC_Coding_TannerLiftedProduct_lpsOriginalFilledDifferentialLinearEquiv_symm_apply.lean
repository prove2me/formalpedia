-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledDifferentialLinearEquiv_symm_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledDifferentialLinearEquiv_symm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:05:10.198312+00:00
-- url     : https://prove2.me/theorems/b2b1e82a-8e8c-4c63-8a20-536e70a2f97f
-- title:
--   Tanner Lifted Product: lps Original Filled Differential Linear Equiv symm apply
-- statement:
--   The inverse equivalence is the genuine cusp form recovered by projection pullback.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicDifferentialComparison.lean#L879-L886
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicDifferentialComparison.lean#L879-L886

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicDifferentialComparison
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledDifferentialLinearEquiv_symm_apply
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalHolomorphicCovectorSections N hN) :
    (lpsOriginalFilledDifferentialLinearEquiv N hN).symm sectionForm =
      lpsOriginalHolomorphicCovectorCuspForm N hN sectionForm := by sorry
