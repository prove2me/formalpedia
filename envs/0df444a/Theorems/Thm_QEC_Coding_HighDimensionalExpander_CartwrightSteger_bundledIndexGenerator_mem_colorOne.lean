-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_bundledIndexGenerator_mem_colorOne
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.bundledIndexGenerator_mem_colorOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:56:26.60629+00:00
-- url     : https://prove2.me/theorems/0d4ef917-7fb6-4f4a-9917-ad9fd4723a21
-- title:
--   Cartwright Steger: bundled Index Generator mem color One
-- statement:
--   The first entry of every full relation occurs as an actual color-one
--   generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L550-L558
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L550-L558

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.bundledIndexGenerator_mem_colorOne
    (P : BasePrime) (r : Rank) (level : Nat)
    {u : Fin r.matrixRank → ConstantProjectiveClass P r}
    (hu : u ∈ buildingRelationTupleFinset P r) :
    bundledIndexGenerator P r level (u (rankZeroIndex r)) ∈
      indexColorGeneratorFinset P r level 1 := by sorry
