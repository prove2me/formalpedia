-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_rankFour_tetrahedron_face_incidence_formula
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.rankFour_tetrahedron_face_incidence_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:36:16.32618+00:00
-- url     : https://prove2.me/theorems/0f93bf18-e886-4715-8d6d-140911f39b63
-- title:
--   Cartwright Steger: rank Four tetrahedron face incidence formula
-- statement:
--   Exact rank-four top-face formula, derived from the actual finite
--   Cartwright--Steger Cayley complex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1496-L1507
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1496-L1507

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.rankFour_tetrahedron_face_incidence_formula
    (P : BasePrime) (level : Nat) :
    4 * Fintype.card
        (SimplicialChain.Face (lsvThreeDimensionalQuotient P level) 4) =
      Fintype.card (IndexFiniteGroup P .four level) *
        Fintype.card
          {σ : SimplicialChain.Face
              (lsvThreeDimensionalQuotient P level) 4 //
            1 ∈ σ.vertices} := by sorry
