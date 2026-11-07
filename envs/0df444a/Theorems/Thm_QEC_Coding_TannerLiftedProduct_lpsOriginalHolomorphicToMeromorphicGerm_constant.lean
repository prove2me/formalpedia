-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicToMeromorphicGerm_constant
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicToMeromorphicGerm_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:59:06.782192+00:00
-- url     : https://prove2.me/theorems/7641b3ff-100b-4a06-9521-ba0421cfb496
-- title:
--   Tanner Lifted Product: lps Original Holomorphic To Meromorphic Germ constant
-- statement:
--   The genuine germ map preserves the actual complex constants.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicGerms.lean#L174-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicGerms.lean#L174-L178

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Algebra.Field.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicGerms
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicToMeromorphicGerm_constant (c : ℂ) :
    lpsOriginalHolomorphicToMeromorphicGerm
      (algebraMap ℂ LPSOriginalHolomorphicRing c) =
      algebraMap ℂ (LPSOriginalMeromorphicGermRing
        UpperHalfPlane.upperHalfPlaneSet) c := by sorry
