-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalSchemeChart_stalkIntegrallyClosed
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalSchemeChart_stalkIntegrallyClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:04:35.087425+00:00
-- url     : https://prove2.me/theorems/8b149e2c-f6a2-46b5-9e1c-0312a883934a
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Scheme Chart stalk Integrally Closed
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Scheme Chart stalk Integrally Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelFunctionField.lean#L123-L140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelFunctionField.lean#L123-L140

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.AlgebraicGeometry.FunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalSchemeChart_stalkIntegrallyClosed
    (N : ℕ) [NeZero N] (hN : 0<N) (b : Bool)
    (y : lpsOriginalIntegerNormalSchemeChart N hN b) :
    IsIntegrallyClosed ((lpsOriginalIntegerNormalSchemeChart N hN b).presheaf.stalk y) := by sorry
