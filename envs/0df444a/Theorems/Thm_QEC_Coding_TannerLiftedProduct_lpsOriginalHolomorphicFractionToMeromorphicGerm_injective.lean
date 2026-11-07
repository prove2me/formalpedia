-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicFractionToMeromorphicGerm_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicFractionToMeromorphicGerm_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:02:55.759714+00:00
-- url     : https://prove2.me/theorems/ba83c50d-7b55-403e-a08d-eff192e60340
-- title:
--   Tanner Lifted Product: lps Original Holomorphic Fraction To Meromorphic Germ injective
-- statement:
--   The holomorphic fraction field embeds faithfully into genuine meromorphic germs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicGerms.lean#L195-L197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicGerms.lean#L195-L197

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicFractionToMeromorphicGerm_injective :
    Function.Injective lpsOriginalHolomorphicFractionToMeromorphicGerm := by sorry
