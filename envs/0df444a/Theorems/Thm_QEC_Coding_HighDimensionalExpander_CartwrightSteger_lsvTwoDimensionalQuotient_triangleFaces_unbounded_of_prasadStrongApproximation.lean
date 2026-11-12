-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_lsvTwoDimensionalQuotient_triangleFaces_unbounded_of_prasadStrongApproximation
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvTwoDimensionalQuotient_triangleFaces_unbounded_of_prasadStrongApproximation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:38:55.209397+00:00
-- url     : https://prove2.me/theorems/8e519c93-c85c-4873-8d47-57857255f491
-- title:
--   Cartwright Steger: lsv Two Dimensional Quotient triangle Faces unbounded of prasad Strong Approximation
-- statement:
--   The triangle counts of the actual two-dimensional LSV quotient hierarchy
--   are unbounded under exactly the Prasad density premise.  The conclusion is
--   derived from the constructed vertex hierarchy and the proved triangle-cover
--   incidence bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1696-L1713
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1696-L1713

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvTwoDimensionalQuotient_triangleFaces_unbounded_of_prasadStrongApproximation
    (P : BasePrime)
    (hPrasad : DenseRange
      (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P .three))
    (bound : Nat) :
    ∃ level, bound < Fintype.card
      (SimplicialChain.Face (lsvTwoDimensionalQuotient P level) 3) := by sorry
