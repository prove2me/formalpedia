-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_splittingCyclicBasis_repr_skewLaurentToGlobalMatrix
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.splittingCyclicBasis_repr_skewLaurentToGlobalMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:24:12.02159+00:00
-- url     : https://prove2.me/theorems/d19d1904-42d4-44ae-a8c9-ec168ef26487
-- title:
--   Cartwright Steger: splitting Cyclic Basis repr skew Laurent To Global Matrix
-- statement:
--   The residue-class Laurent coordinate formula for an arbitrary skew
--   Laurent polynomial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewFaithfulness.lean#L142-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewFaithfulness.lean#L142-L162

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewResidueCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewFaithfulness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.splittingCyclicBasis_repr_skewLaurentToGlobalMatrix
    (P : BasePrime) (r : Rank)
    (f : CartwrightStegerSkewLaurentRing P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (splittingCyclicBasis P r).repr
        (skewLaurentToGlobalMatrix P r f) p =
      algebraMap (FunctionField P) (SplittingFunctionField P r)
        (functionFieldOnePlusYLaurentEvaluation P
          (skewLaurentCyclicLaurentCoordinate P r f p)) := by sorry
