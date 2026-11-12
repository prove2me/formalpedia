-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_indexColorGeneratorFinset_iff_exists_buildingRelation
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_indexColorGeneratorFinset_iff_exists_buildingRelation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:27:46.020345+00:00
-- url     : https://prove2.me/theorems/c97103cc-167a-4c6f-b2d8-1185e6bf52b3
-- title:
--   Cartwright Steger: mem index Color Generator Finset iff exists building Relation
-- statement:
--   Membership in a finite color has a witness in the fixed global building
--   relation system.  Hence congruence-only short relations cannot create new
--   colored generators or faces.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L484-L491
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L484-L491

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_indexColorGeneratorFinset_iff_exists_buildingRelation
    (P : BasePrime) (r : Rank) (level k : Nat)
    (g : IndexFiniteGroup P r level) :
    g ∈ indexColorGeneratorFinset P r level k ↔
      ∃ u ∈ buildingRelationTupleFinset P r,
        indexGeneratorPrefixProduct P r level k u = g := by sorry
