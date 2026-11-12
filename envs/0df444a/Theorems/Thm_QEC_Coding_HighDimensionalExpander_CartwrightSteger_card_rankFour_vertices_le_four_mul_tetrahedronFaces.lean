-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_card_rankFour_vertices_le_four_mul_tetrahedronFaces
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_rankFour_vertices_le_four_mul_tetrahedronFaces
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:59:56.724596+00:00
-- url     : https://prove2.me/theorems/3b8e7eaf-5848-4646-9cc6-d2418ce3b2c4
-- title:
--   Cartwright Steger: card rank Four vertices le four mul tetrahedron Faces
-- statement:
--   The rank-four tetrahedron count controls the full vertex count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1334-L1340
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1334-L1340

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_rankFour_vertices_le_four_mul_tetrahedronFaces
    (P : BasePrime) (level : Nat) :
    Fintype.card (IndexFiniteGroup P .four level) ≤
      4 * Fintype.card
        (SimplicialChain.Face (lsvThreeDimensionalQuotient P level) 4) := by sorry
