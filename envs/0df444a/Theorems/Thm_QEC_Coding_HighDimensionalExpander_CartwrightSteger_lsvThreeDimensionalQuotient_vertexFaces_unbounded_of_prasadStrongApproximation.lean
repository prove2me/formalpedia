-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_lsvThreeDimensionalQuotient_vertexFaces_unbounded_of_prasadStrongApproximation
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvThreeDimensionalQuotient_vertexFaces_unbounded_of_prasadStrongApproximation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:39:23.033306+00:00
-- url     : https://prove2.me/theorems/e556a463-745f-4953-b899-a5980e06d4d5
-- title:
--   Cartwright Steger: lsv Three Dimensional Quotient vertex Faces unbounded of prasad Strong Approximation
-- statement:
--   The rank-four / three-dimensional LSV quotient hierarchy has unbounded
--   vertex count under exactly the Prasad density premise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1681-L1690
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1681-L1690

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvThreeDimensionalQuotient_vertexFaces_unbounded_of_prasadStrongApproximation
    (P : BasePrime)
    (hPrasad : DenseRange
      (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P .four))
    (bound : Nat) :
    ∃ level, bound < Fintype.card
      (SimplicialChain.Face (lsvThreeDimensionalQuotient P level) 1) := by sorry
