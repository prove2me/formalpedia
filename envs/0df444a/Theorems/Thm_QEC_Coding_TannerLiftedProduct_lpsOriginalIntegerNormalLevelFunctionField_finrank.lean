-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalLevelFunctionField_finrank
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalLevelFunctionField_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:14:24.633075+00:00
-- url     : https://prove2.me/theorems/f323b744-fd2b-4ccd-ba72-ff771738e49e
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Level Function Field finrank
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Level Function Field finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L331-L359
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L331-L359

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalLevelFunctionField_finrank
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    letI := (lpsOriginalIntegerNormalLevelFunctionFieldPullback N M hNM h4N hN hM).toAlgebra
    Module.finrank (lpsOriginalIntegerNormalGluedScheme N hN).functionField
      (lpsOriginalIntegerNormalGluedScheme M hM).functionField =
        (lpsOriginalGeneratedFunctionFieldQ N hN).relfinrank
          (lpsOriginalGeneratedFunctionFieldQ M hM) := by sorry
