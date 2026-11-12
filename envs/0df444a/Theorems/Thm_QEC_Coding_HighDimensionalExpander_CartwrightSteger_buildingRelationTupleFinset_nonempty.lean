-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingRelationTupleFinset_nonempty
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingRelationTupleFinset_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:40:22.932723+00:00
-- url     : https://prove2.me/theorems/f3aba6a8-ab57-450d-8374-a3e02c670cfb
-- title:
--   Cartwright Steger: building Relation Tuple Finset nonempty
-- statement:
--   The construction-owned relation set is genuinely nonempty.  Its witness
--   is the rank-three or rank-four apartment loop, transported through the actual
--   arithmetic order and congruence reduction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L419-L436
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L419-L436

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
set_option maxHeartbeats 1000000

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingRelationTupleFinset_nonempty
    (P : BasePrime) (r : Rank) :
    (buildingRelationTupleFinset P r).Nonempty := by sorry
