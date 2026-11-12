-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexColorGeneratorFinset_subset_colored
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexColorGeneratorFinset_subset_colored
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:42:54.493842+00:00
-- url     : https://prove2.me/theorems/6289195e-f405-46b7-af2b-280bbcccf51e
-- title:
--   Cartwright Steger: index Color Generator Finset subset colored
-- statement:
--   The Cartwright Steger construction uses the index Color Generator Finset subset colored property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L663-L670
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L663-L670

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexColorGeneratorFinset_subset_colored
    (P : BasePrime) (r : Rank) (level k : Nat)
    (hk : k ∈ Finset.Icc 1 (r.matrixRank - 1)) :
    indexColorGeneratorFinset P r level k ⊆
      indexColoredGeneratorFinset P r level := by sorry
