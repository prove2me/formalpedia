-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalLevelFunctionFieldPullback_naturality
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalLevelFunctionFieldPullback_naturality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:12:34.835727+00:00
-- url     : https://prove2.me/theorems/327ec86d-62aa-43d2-8747-b36f6e30ddbc
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Level Function Field Pullback naturality
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Level Function Field Pullback naturality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L287-L318
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L287-L318

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalLevelFunctionFieldPullback_naturality
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    (lpsOriginalIntegerNormalGluedFunctionFieldEquiv M hM).toRingHom.comp
      (lpsOriginalIntegerNormalLevelFunctionFieldPullback N M hNM h4N hN hM) =
    (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom.comp
      (lpsOriginalIntegerNormalGluedFunctionFieldEquiv N hN).toRingHom := by sorry
