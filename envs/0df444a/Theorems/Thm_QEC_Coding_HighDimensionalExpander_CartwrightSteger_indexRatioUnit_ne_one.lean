-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexRatioUnit_ne_one
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexRatioUnit_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:37:27.031207+00:00
-- url     : https://prove2.me/theorems/412fa8ae-8e12-41ca-a0ca-9001c47d244e
-- title:
--   Cartwright Steger: index Ratio Unit ne one
-- statement:
--   The Cartwright Steger construction uses the index Ratio Unit ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSelection.lean#L371-L376
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSelection.lean#L371-L376

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open IntermediateField
open IndexSelection

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexRatioUnit_ne_one
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexRatioUnit P r level ≠ 1 := by sorry
