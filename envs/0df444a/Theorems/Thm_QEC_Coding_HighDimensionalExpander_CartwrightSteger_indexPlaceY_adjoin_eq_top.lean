-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexPlaceY_adjoin_eq_top
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexPlaceY_adjoin_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:35:07.677442+00:00
-- url     : https://prove2.me/theorems/4da19955-71f0-4d51-88a6-431a42c9ca88
-- title:
--   Cartwright Steger: index Place Y adjoin eq top
-- statement:
--   The Cartwright Steger construction uses the index Place Y adjoin eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSelection.lean#L301-L303
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSelection.lean#L301-L303

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open IntermediateField
open IndexSelection

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexPlaceY_adjoin_eq_top (P : BasePrime) (r : Rank) (level : Nat) :
    (BaseField P)⟮indexPlaceY P r level⟯ = ⊤ := by sorry
