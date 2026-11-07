-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGenericStalkMap_fromSpec
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGenericStalkMap_fromSpec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:12:29.864647+00:00
-- url     : https://prove2.me/theorems/851166c2-785e-4f95-85d2-ccc2ef4397f1
-- title:
--   Tanner Lifted Product: lps Original Generic Stalk Map from Spec
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Generic Stalk Map from Spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L196-L202
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L196-L202

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGenericStalkMap_fromSpec {X Y : Scheme}
    (f : Y ⟶ X) (y : Y) (x : X) (h : f y = x) :
    Spec.map (eqToHom (congrArg X.presheaf.stalk h.symm) ≫ f.stalkMap y) ≫
      X.fromSpecStalk x = Y.fromSpecStalk y ≫ f := by sorry
