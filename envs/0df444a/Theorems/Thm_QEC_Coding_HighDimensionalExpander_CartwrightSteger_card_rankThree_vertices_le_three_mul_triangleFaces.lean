-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_card_rankThree_vertices_le_three_mul_triangleFaces
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_rankThree_vertices_le_three_mul_triangleFaces
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:59:48.28429+00:00
-- url     : https://prove2.me/theorems/061b4b3d-e626-4d6f-8b00-8b912261d929
-- title:
--   Cartwright Steger: card rank Three vertices le three mul triangle Faces
-- statement:
--   The rank-three triangle count controls the full vertex count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1325-L1331
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1325-L1331

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_rankThree_vertices_le_three_mul_triangleFaces
    (P : BasePrime) (level : Nat) :
    Fintype.card (IndexFiniteGroup P .three level) ≤
      3 * Fintype.card
        (SimplicialChain.Face (lsvTwoDimensionalQuotient P level) 3) := by sorry
