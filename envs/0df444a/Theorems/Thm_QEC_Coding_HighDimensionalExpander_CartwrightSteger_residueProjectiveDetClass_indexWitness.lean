-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueProjectiveDetClass_indexWitness
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueProjectiveDetClass_indexWitness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:38:49.251137+00:00
-- url     : https://prove2.me/theorems/15b8ebf5-3a3a-492f-afdc-ade83b3cfca4
-- title:
--   Cartwright Steger: residue Projective Det Class index Witness
-- statement:
--   The Cartwright Steger construction uses the residue Projective Det Class index Witness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/FiniteImage.lean#L96-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/FiniteImage.lean#L96-L105

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_FiniteImage
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueProjectiveDetClass_indexWitness
    (P : BasePrime) (r : Rank) (level : Nat) :
    residueProjectiveDetClass P r level (indexWitness P r level) =
      (QuotientGroup.mk (indexRatioUnit P r level) :
        ResiduePowerClass P r level) := by sorry
