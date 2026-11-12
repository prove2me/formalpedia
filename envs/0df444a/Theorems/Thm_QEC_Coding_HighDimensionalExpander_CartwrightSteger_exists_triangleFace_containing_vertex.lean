-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_triangleFace_containing_vertex
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_triangleFace_containing_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:59:35.463786+00:00
-- url     : https://prove2.me/theorems/59b6565a-7018-4490-a65a-d5afd4ac541c
-- title:
--   Cartwright Steger: exists triangle Face containing vertex
-- statement:
--   Every vertex of the rank-three quotient lies in a triangular chamber,
--   by translating the construction-owned chamber with the Cayley action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L932-L941
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L932-L941

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_triangleFace_containing_vertex
    (P : BasePrime) (level : Nat)
    (x : IndexFiniteGroup P .three level) :
    ∃ σ : SimplicialChain.Face
        (lsvTwoDimensionalQuotient P level) 3,
      x ∈ σ.vertices := by sorry
