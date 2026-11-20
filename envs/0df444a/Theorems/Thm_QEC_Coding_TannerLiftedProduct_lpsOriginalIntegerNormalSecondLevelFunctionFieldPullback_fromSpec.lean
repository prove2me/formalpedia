-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback_fromSpec
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback_fromSpec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:53:40.508356+00:00
-- url     : https://prove2.me/theorems/0afd6d54-91a4-4581-a817-b46db1163993
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Second Level Function Field Pullback from Spec
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Second Level Function Field Pullback from Spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSecondIntegerHecke.lean#L225-L243
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSecondIntegerHecke.lean#L225-L243

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback_fromSpec
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    Spec.map (CommRingCat.ofHom
      (lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback N M hNM h4N hN hM)) ≫
      (lpsOriginalIntegerNormalGluedScheme N hN).fromSpecStalk
        (genericPoint (lpsOriginalIntegerNormalGluedScheme N hN)) =
      (lpsOriginalIntegerNormalGluedScheme M hM).fromSpecStalk
        (genericPoint (lpsOriginalIntegerNormalGluedScheme M hM)) ≫
          lpsOriginalIntegerNormalGluedSecondLevelMap N M hNM h4N hN hM := by sorry
