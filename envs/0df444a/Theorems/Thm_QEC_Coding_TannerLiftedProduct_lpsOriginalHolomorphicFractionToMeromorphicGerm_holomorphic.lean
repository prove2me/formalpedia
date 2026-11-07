-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:58:28.224736+00:00
-- url     : https://prove2.me/theorems/8721b713-7176-49a9-b6d1-4daa7270b084
-- title:
--   Tanner Lifted Product: lps Original Holomorphic Fraction To Meromorphic Germ holomorphic
-- statement:
--   The actual fraction embedding agrees with the original holomorphic germ map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicGerms.lean#L187-L192
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicGerms.lean#L187-L192

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic
    (f : LPSOriginalHolomorphicRing) :
    lpsOriginalHolomorphicFractionToMeromorphicGerm
      (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField f) =
      lpsOriginalHolomorphicToMeromorphicGerm f := by sorry
