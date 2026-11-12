-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_cyclicAlgebraReducedNormPolynomial
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_cyclicAlgebraReducedNormPolynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:21:46.342284+00:00
-- url     : https://prove2.me/theorems/9b6c2643-a296-4a0d-92f3-135a500e3fd7
-- title:
--   Cartwright Steger: map cyclic Algebra Reduced Norm Polynomial
-- statement:
--   The Cartwright Steger construction uses the map cyclic Algebra Reduced Norm Polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L427-L439
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/IntrinsicNorm.lean#L427-L439

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_cyclicAlgebraReducedNormPolynomial
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    Polynomial.map (functionFieldEmbedding P r)
        (cyclicAlgebraReducedNormPolynomial P r x) =
      Matrix.affineLineDet
        (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) := by sorry
