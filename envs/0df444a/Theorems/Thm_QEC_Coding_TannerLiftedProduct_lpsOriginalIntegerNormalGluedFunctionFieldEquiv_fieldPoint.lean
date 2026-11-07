-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedFunctionFieldEquiv_fieldPoint
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedFunctionFieldEquiv_fieldPoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:12:08.919707+00:00
-- url     : https://prove2.me/theorems/139aca3b-0733-4515-86c0-ca9ae1773e85
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Glued Function Field Equiv field Point
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Glued Function Field Equiv field Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L226-L264
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L226-L264

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedFunctionFieldEquiv_fieldPoint
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    Spec.map (CommRingCat.ofHom
      (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN).toRingHom) ≫
      (lpsOriginalIntegerNormalGluedScheme N hN).fromSpecStalk
        (genericPoint (lpsOriginalIntegerNormalGluedScheme N hN)) =
      lpsOriginalIntegerNormalGeneratedFieldPoint N hN := by sorry
