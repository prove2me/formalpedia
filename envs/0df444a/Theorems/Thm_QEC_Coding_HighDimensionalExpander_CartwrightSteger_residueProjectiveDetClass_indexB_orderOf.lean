-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueProjectiveDetClass_indexB_orderOf
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueProjectiveDetClass_indexB_orderOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:47:58.407199+00:00
-- url     : https://prove2.me/theorems/f3234ab5-8863-4eea-95c7-f96e4008ff54
-- title:
--   Cartwright Steger: residue Projective Det Class index B order Of
-- statement:
--   The Cartwright Steger construction uses the residue Projective Det Class index B order Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L147-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L147-L153

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueProjectiveDetClass_indexB_orderOf
    (P : BasePrime) (r : Rank) (level : Nat) :
    orderOf (residueProjectiveDetClass P r level (indexB P r level)) =
      Nat.card (ResiduePowerClass P r level) := by sorry
