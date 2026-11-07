-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_ker_residueProjectiveDetClass_eq_PSL
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.ker_residueProjectiveDetClass_eq_PSL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:36:26.1853+00:00
-- url     : https://prove2.me/theorems/f47bf137-3200-4073-99b6-5a05a9d26558
-- title:
--   Cartwright Steger: ker residue Projective Det Class eq PSL
-- statement:
--   The Cartwright Steger construction uses the ker residue Projective Det Class eq PSL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Index.lean#L163-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Index.lean#L163-L172

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.ker_residueProjectiveDetClass_eq_PSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    (residueProjectiveDetClass P r level).ker = PSL P r level := by sorry
