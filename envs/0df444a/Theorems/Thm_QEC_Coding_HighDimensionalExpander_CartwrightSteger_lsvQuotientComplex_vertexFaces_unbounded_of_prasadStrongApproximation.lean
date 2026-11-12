-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_lsvQuotientComplex_vertexFaces_unbounded_of_prasadStrongApproximation
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvQuotientComplex_vertexFaces_unbounded_of_prasadStrongApproximation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:46:27.205058+00:00
-- url     : https://prove2.me/theorems/027654c9-a722-43e3-a17e-6bd27f802f97
-- title:
--   Cartwright Steger: lsv Quotient Complex vertex Faces unbounded of prasad Strong Approximation
-- statement:
--   Under the sole construction-specialized Prasad density premise, the
--   zero-dimensional face counts of the actual finite LSV quotient complexes are
--   unbounded.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1651-L1664
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1651-L1664

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvQuotientComplex_vertexFaces_unbounded_of_prasadStrongApproximation
    (P : BasePrime) (r : Rank)
    (hPrasad : DenseRange
      (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r))
    (bound : Nat) :
    ∃ level, bound < Fintype.card
      (SimplicialChain.Face (lsvQuotientComplex P r level) 1) := by sorry
