-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_splittingCyclicBasis_repr_skewLaurentToGlobalMatrix_single
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.splittingCyclicBasis_repr_skewLaurentToGlobalMatrix_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:23:24.978839+00:00
-- url     : https://prove2.me/theorems/0c424289-04c2-46ab-a21e-cb79f7d0aab5
-- title:
--   Cartwright Steger: splitting Cyclic Basis repr skew Laurent To Global Matrix single
-- statement:
--   On a single skew monomial, each matrix-basis coordinate is the evaluation
--   at `1 + y` of the corresponding residue-class Laurent coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewFaithfulness.lean#L76-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewFaithfulness.lean#L76-L138

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewResidueCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewFaithfulness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.splittingCyclicBasis_repr_skewLaurentToGlobalMatrix_single
    (P : BasePrime) (r : Rank) (m : Multiplicative ℤ)
    (c : ConstantExtension P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (splittingCyclicBasis P r).repr
        (skewLaurentToGlobalMatrix P r
          (SkewMonoidAlgebra.single m c)) p =
      algebraMap (FunctionField P) (SplittingFunctionField P r)
        (functionFieldOnePlusYLaurentEvaluation P
          (skewLaurentCyclicLaurentCoordinate P r
            (SkewMonoidAlgebra.single m c) p)) := by sorry
