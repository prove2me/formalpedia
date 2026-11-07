-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_det_one_sub_inv_of_charpoly_eq_X_pow_sub_C_one_add
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.det_one_sub_inv_of_charpoly_eq_X_pow_sub_C_one_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:42:22.105268+00:00
-- url     : https://prove2.me/theorems/493afb0c-745f-40a8-a8e1-3c2ece0ad414
-- title:
--   Cartwright Steger: det one sub inv of charpoly eq X pow sub C one add
-- statement:
--   Matrix form of LSV Proposition `normb`, specialized only to the two
--   construction ranks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/Norm.lean#L18-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/Norm.lean#L18-L70

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_FiniteImage
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.det_one_sub_inv_of_charpoly_eq_X_pow_sub_C_one_add
    {K : Type*} [Field K] (r : Rank)
    (z : Matrix.GeneralLinearGroup (Fin r.matrixRank) K) (y : K)
    (hchar : (z : Matrix (Fin r.matrixRank) (Fin r.matrixRank) K).charpoly =
      Polynomial.X ^ r.matrixRank - Polynomial.C (1 + y)) :
    Matrix.det
        ((1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank) K) -
          ((z⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank) K) :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank) K)) =
      y / (1 + y) := by sorry
