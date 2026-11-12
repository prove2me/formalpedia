-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_card_indexGeneratorFinset_le
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_indexGeneratorFinset_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:19:37.587432+00:00
-- url     : https://prove2.me/theorems/7a56757c-1a29-445f-be81-bb3da1396d63
-- title:
--   Cartwright Steger: card index Generator Finset le
-- statement:
--   The Cartwright Steger construction uses the card index Generator Finset le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L192-L196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L192-L196

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_indexGeneratorFinset_le
    (P : BasePrime) (r : Rank) (level : Nat) :
    (indexGeneratorFinset P r level).card ≤
      Fintype.card (ConstantProjectiveClass P r) := by sorry
