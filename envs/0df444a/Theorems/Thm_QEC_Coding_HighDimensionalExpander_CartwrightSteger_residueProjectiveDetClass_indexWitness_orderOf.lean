-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueProjectiveDetClass_indexWitness_orderOf
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueProjectiveDetClass_indexWitness_orderOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:38:33.112077+00:00
-- url     : https://prove2.me/theorems/5359b267-d477-4494-bd80-c0977c37788d
-- title:
--   Cartwright Steger: residue Projective Det Class index Witness order Of
-- statement:
--   The Cartwright Steger construction uses the residue Projective Det Class index Witness order Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/FiniteImage.lean#L107-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/FiniteImage.lean#L107-L114

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_FiniteImage
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueProjectiveDetClass_indexWitness_orderOf
    (P : BasePrime) (r : Rank) (level : Nat) :
    orderOf
        (residueProjectiveDetClass P r level (indexWitness P r level)) =
      Nat.card (ResiduePowerClass P r level) := by sorry
