-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexGeneratorBound_mul_baseScalar
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexGeneratorBound_mul_baseScalar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:20:44.889643+00:00
-- url     : https://prove2.me/theorems/21c13b68-4d06-47ee-a1ba-0ff7f9afc0fd
-- title:
--   Cartwright Steger: index Generator Bound mul base Scalar
-- statement:
--   Exact source-size equation for the hierarchy's projective generator
--   index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L213-L218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L213-L218

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexGeneratorBound_mul_baseScalar
    (P : BasePrime) (r : Rank) :
    indexGeneratorBound P r * (P.q - 1) =
      P.q ^ r.matrixRank - 1 := by sorry
