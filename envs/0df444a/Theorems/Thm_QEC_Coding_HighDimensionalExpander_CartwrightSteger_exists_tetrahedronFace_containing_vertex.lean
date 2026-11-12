-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_tetrahedronFace_containing_vertex
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_tetrahedronFace_containing_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:59:37.725396+00:00
-- url     : https://prove2.me/theorems/1c02e615-a7f0-4327-bb63-fdb5e5abf6ad
-- title:
--   Cartwright Steger: exists tetrahedron Face containing vertex
-- statement:
--   Every vertex of the rank-four quotient lies in a tetrahedral chamber,
--   again by the genuine Cayley left action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1148-L1157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1148-L1157

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_tetrahedronFace_containing_vertex
    (P : BasePrime) (level : Nat)
    (x : IndexFiniteGroup P .four level) :
    ∃ σ : SimplicialChain.Face
        (lsvThreeDimensionalQuotient P level) 4,
      x ∈ σ.vertices := by sorry
