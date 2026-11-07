-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_IndexCartwrightStegerStabilizer_le_normalizer_image
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.IndexCartwrightStegerStabilizer_le_normalizer_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:48:28.155364+00:00
-- url     : https://prove2.me/theorems/70729999-fef8-4702-bdc5-22ef31a743a8
-- title:
--   Cartwright Steger: Index Cartwright Steger Stabilizer le normalizer image
-- statement:
--   The Cartwright Steger construction uses the Index Cartwright Steger Stabilizer le normalizer image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L716-L722
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L716-L722

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.IndexCartwrightStegerStabilizer_le_normalizer_image
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCartwrightStegerStabilizer P r level ≤
      Subgroup.normalizer
        (IndexCartwrightStegerImage P r level : Set _) := by sorry
