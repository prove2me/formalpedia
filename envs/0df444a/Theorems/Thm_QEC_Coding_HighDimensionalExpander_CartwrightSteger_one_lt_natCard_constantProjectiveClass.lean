-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_one_lt_natCard_constantProjectiveClass
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.one_lt_natCard_constantProjectiveClass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:47:54.18622+00:00
-- url     : https://prove2.me/theorems/2d9cd92e-a483-4a32-b97f-301fc339bfc6
-- title:
--   Cartwright Steger: one lt nat Card constant Projective Class
-- statement:
--   The Cartwright Steger construction uses the one lt nat Card constant Projective Class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L537-L564
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L537-L564

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.one_lt_natCard_constantProjectiveClass
    (P : BasePrime) (r : Rank) :
    1 < Nat.card (ConstantProjectiveClass P r) := by sorry
