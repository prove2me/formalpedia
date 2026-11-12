-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_card_indexGeneratorFinset
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_indexGeneratorFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:55:46.375358+00:00
-- url     : https://prove2.me/theorems/9c099899-5428-4e44-9c12-f2f5ce8378fb
-- title:
--   Cartwright Steger: card index Generator Finset
-- statement:
--   The finite generating set has exactly the source projective-line size;
--   no repetitions are hidden by the selected representatives.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L183-L190
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L183-L190

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_indexGeneratorFinset
    (P : BasePrime) (r : Rank) (level : Nat) :
    (indexGeneratorFinset P r level).card =
      Fintype.card (ConstantProjectiveClass P r) := by sorry
