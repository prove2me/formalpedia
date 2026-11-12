-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_rankThree_triangle_face_incidence_formula
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.rankThree_triangle_face_incidence_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:36:18.184302+00:00
-- url     : https://prove2.me/theorems/b712a4da-0fb9-444f-9ccb-b7a613c956d0
-- title:
--   Cartwright Steger: rank Three triangle face incidence formula
-- statement:
--   Exact rank-three top-face formula, derived from the actual finite
--   Cartwright--Steger Cayley complex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1481-L1492
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1481-L1492

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.rankThree_triangle_face_incidence_formula
    (P : BasePrime) (level : Nat) :
    3 * Fintype.card
        (SimplicialChain.Face (lsvTwoDimensionalQuotient P level) 3) =
      Fintype.card (IndexFiniteGroup P .three level) *
        Fintype.card
          {σ : SimplicialChain.Face
              (lsvTwoDimensionalQuotient P level) 3 //
            1 ∈ σ.vertices} := by sorry
