-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_image_buildingColorGeneratorFinset_reduction
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.image_buildingColorGeneratorFinset_reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:55:47.877267+00:00
-- url     : https://prove2.me/theorems/1bc8d155-362a-438f-b748-dd5c52762fc1
-- title:
--   Cartwright Steger: image building Color Generator Finset reduction
-- statement:
--   A finite color is exactly the congruence image of the corresponding
--   level-independent building color.  Thus the finite complex has neither
--   omitted building colors nor congruence-only extra colors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L463-L479
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L463-L479

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.image_buildingColorGeneratorFinset_reduction
    (P : BasePrime) (r : Rank) (level k : Nat) :
    (buildingColorGeneratorFinset P r k).image
        (buildingLatticeFiniteReduction P r level) =
      indexColorGeneratorFinset P r level k := by sorry
