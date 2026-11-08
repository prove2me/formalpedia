-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedScheme_stalkIntegrallyClosed
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedScheme_stalkIntegrallyClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:57:32.190787+00:00
-- url     : https://prove2.me/theorems/37dc573a-0881-4995-ae91-06d4f7ce9660
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Glued Scheme stalk Integrally Closed
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Glued Scheme stalk Integrally Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelFunctionField.lean#L142-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelFunctionField.lean#L142-L150

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.AlgebraicGeometry.FunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedScheme_stalkIntegrallyClosed
    (N : ℕ) [NeZero N] (hN : 0<N)
    (x : lpsOriginalIntegerNormalGluedScheme N hN) :
    IsIntegrallyClosed ((lpsOriginalIntegerNormalGluedScheme N hN).presheaf.stalk x) := by sorry
