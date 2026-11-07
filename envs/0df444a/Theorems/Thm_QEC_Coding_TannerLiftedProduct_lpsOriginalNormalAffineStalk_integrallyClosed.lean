-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalAffineStalk_integrallyClosed
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNormalAffineStalk_integrallyClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:04:50.556904+00:00
-- url     : https://prove2.me/theorems/e53c9b80-7dc9-46d9-9356-d5d03af830f8
-- title:
--   Tanner Lifted Product: lps Original Normal Affine Stalk integrally Closed
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Normal Affine Stalk integrally Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelFunctionField.lean#L114-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelFunctionField.lean#L114-L121

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.AlgebraicGeometry.FunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNormalAffineStalk_integrallyClosed
    (R : CommRingCat) [IsDomain R] [IsIntegrallyClosed R] (y : Spec R) :
    IsIntegrallyClosed ((Spec R).presheaf.stalk y) := by sorry
