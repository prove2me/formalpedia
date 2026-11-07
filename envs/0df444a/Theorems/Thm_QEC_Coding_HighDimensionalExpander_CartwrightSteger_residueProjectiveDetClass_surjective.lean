-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueProjectiveDetClass_surjective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueProjectiveDetClass_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:42:04.90619+00:00
-- url     : https://prove2.me/theorems/8e8b4139-e989-41d7-be90-36627c85e31f
-- title:
--   Cartwright Steger: residue Projective Det Class surjective
-- statement:
--   The Cartwright Steger construction uses the residue Projective Det Class surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Index.lean#L174-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Index.lean#L174-L182

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueProjectiveDetClass_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (residueProjectiveDetClass P r level) := by sorry
