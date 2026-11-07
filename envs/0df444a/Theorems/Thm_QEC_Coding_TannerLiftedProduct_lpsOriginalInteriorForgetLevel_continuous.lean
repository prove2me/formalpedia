-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInteriorForgetLevel_continuous
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalInteriorForgetLevel_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:21:10.888204+00:00
-- url     : https://prove2.me/theorems/6d3f98db-4218-4319-bb3f-acd4e3753db7
-- title:
--   Tanner Lifted Product: lps Original Interior Forget Level continuous
-- statement:
--   The canonical original level quotient map is continuous by actual quotient descent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L272-L275
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L272-L275

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalInteriorForgetLevel_continuous (N M : ℕ) (hNM : N ∣ M) :
    Continuous (lpsOriginalInteriorForgetLevel N M hNM) := by sorry
