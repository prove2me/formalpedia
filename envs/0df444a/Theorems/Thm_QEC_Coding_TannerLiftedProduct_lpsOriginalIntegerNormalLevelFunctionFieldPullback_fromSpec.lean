-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalLevelFunctionFieldPullback_fromSpec
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalLevelFunctionFieldPullback_fromSpec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:13:06.439428+00:00
-- url     : https://prove2.me/theorems/1fae7e21-3f13-46b5-9da3-60ee453b1385
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Level Function Field Pullback from Spec
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Level Function Field Pullback from Spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L266-L284
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L266-L284

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalLevelFunctionFieldPullback_fromSpec
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    Spec.map (CommRingCat.ofHom
      (lpsOriginalIntegerNormalLevelFunctionFieldPullback N M hNM h4N hN hM)) ≫
      (lpsOriginalIntegerNormalGluedScheme N hN).fromSpecStalk
        (genericPoint (lpsOriginalIntegerNormalGluedScheme N hN)) =
      (lpsOriginalIntegerNormalGluedScheme M hM).fromSpecStalk
        (genericPoint (lpsOriginalIntegerNormalGluedScheme M hM)) ≫
          lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM := by sorry
