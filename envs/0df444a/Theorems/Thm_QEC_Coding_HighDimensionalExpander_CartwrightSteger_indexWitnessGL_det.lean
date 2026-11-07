-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexWitnessGL_det
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexWitnessGL_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:38:43.445501+00:00
-- url     : https://prove2.me/theorems/9413ffea-a72f-4010-b84c-b59563887b89
-- title:
--   Cartwright Steger: index Witness GL det
-- statement:
--   The Cartwright Steger construction uses the index Witness GL det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/FiniteImage.lean#L82-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/FiniteImage.lean#L82-L89

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_FiniteImage
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexWitnessGL_det
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.GeneralLinearGroup.det (indexWitnessGL P r level) =
      indexRatioUnit P r level := by sorry
