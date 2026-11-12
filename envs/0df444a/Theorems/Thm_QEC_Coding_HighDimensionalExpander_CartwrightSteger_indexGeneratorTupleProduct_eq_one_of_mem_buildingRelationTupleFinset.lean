-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexGeneratorTupleProduct_eq_one_of_mem_buildingRelationTupleFinset
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexGeneratorTupleProduct_eq_one_of_mem_buildingRelationTupleFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:22:06.529101+00:00
-- url     : https://prove2.me/theorems/94e61eeb-c81f-4fc9-9a15-8dbdc879a260
-- title:
--   Cartwright Steger: index Generator Tuple Product eq one of mem building Relation Tuple Finset
-- statement:
--   A genuine building relation remains a rank-length relation in every
--   selected congruence image.  The converse is deliberately not used: a finite
--   quotient can contain additional short words equal to one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L441-L449
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L441-L449

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexGeneratorTupleProduct_eq_one_of_mem_buildingRelationTupleFinset
    (P : BasePrime) (r : Rank) (level : Nat)
    {u : Fin r.matrixRank → ConstantProjectiveClass P r}
    (hu : u ∈ buildingRelationTupleFinset P r) :
    indexGeneratorTupleProduct P r level u = 1 := by sorry
