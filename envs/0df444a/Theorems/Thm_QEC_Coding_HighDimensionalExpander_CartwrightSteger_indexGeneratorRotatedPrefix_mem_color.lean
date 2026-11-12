-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexGeneratorRotatedPrefix_mem_color
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexGeneratorRotatedPrefix_mem_color
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:42:11.838725+00:00
-- url     : https://prove2.me/theorems/85a9c29b-0dd6-43c5-8236-bc189fff06f4
-- title:
--   Cartwright Steger: index Generator Rotated Prefix mem color
-- statement:
--   Every cyclic segment of a construction-owned relation appears in its
--   corresponding color.  Rotation is justified by the relation product itself,
--   not postulated as extra combinatorial input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L529-L546
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L529-L546

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexGeneratorRotatedPrefix_mem_color
    (P : BasePrime) (r : Rank) (level : Nat)
    {u : Fin r.matrixRank → ConstantProjectiveClass P r}
    (hu : u ∈ buildingRelationTupleFinset P r)
    (n k : Nat) :
    indexGeneratorWordProduct P r level
        (((List.ofFn u).rotate n).take k) ∈
      indexColorGeneratorFinset P r level k := by sorry
