-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntermediateFieldInclusion_finrank
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntermediateFieldInclusion_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:12:30.061684+00:00
-- url     : https://prove2.me/theorems/55f24929-fc75-4702-b1b1-8e22ab83339b
-- title:
--   Tanner Lifted Product: lps Original Intermediate Field Inclusion finrank
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Intermediate Field Inclusion finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L321-L328
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L321-L328

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntermediateFieldInclusion_finrank
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A B : IntermediateField K L) (h : A ≤ B) :
    letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
    Module.finrank A B = A.relfinrank B := by sorry
