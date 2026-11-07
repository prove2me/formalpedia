-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecFromStalk_transport
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSpecFromStalk_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:12:23.905209+00:00
-- url     : https://prove2.me/theorems/f58312c6-d61d-4b48-98ba-e4d9a0100ff0
-- title:
--   Tanner Lifted Product: lps Original Spec From Stalk transport
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Spec From Stalk transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L190-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L190-L194

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSpecFromStalk_transport (X : Scheme) (x y : X) (h : x = y) :
    Spec.map (eqToHom (congrArg X.presheaf.stalk h)) ≫ X.fromSpecStalk x =
      X.fromSpecStalk y := by sorry
