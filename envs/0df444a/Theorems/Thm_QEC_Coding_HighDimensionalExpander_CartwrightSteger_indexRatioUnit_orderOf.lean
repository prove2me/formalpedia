-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexRatioUnit_orderOf
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexRatioUnit_orderOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:34:48.29341+00:00
-- url     : https://prove2.me/theorems/414aae58-8053-4037-838d-0a62b069df3a
-- title:
--   Cartwright Steger: index Ratio Unit order Of
-- statement:
--   The Cartwright Steger construction uses the index Ratio Unit order Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSelection.lean#L305-L310
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSelection.lean#L305-L310

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open IntermediateField
open IndexSelection

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexRatioUnit_orderOf (P : BasePrime) (r : Rank) (level : Nat) :
    orderOf
      (QuotientGroup.mk (indexRatioUnit P r level) :
        ResiduePowerClass P r level) =
      (Fintype.card (ResidueField P r level) - 1).gcd r.matrixRank := by sorry
