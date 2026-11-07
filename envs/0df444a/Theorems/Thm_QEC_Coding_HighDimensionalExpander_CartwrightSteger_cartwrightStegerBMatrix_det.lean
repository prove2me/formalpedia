-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerBMatrix_det
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerBMatrix_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:39:16.159324+00:00
-- url     : https://prove2.me/theorems/3a25adb3-2411-4330-846e-bff392fbef21
-- title:
--   Cartwright Steger: cartwright Steger BMatrix det
-- statement:
--   LSV Proposition `normb` for the construction-owned split cyclic algebra:
--   the determinant (hence reduced norm) of `b = 1 - z⁻¹` is exactly
--   `y / (1 + y)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/Norm.lean#L148-L155
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/Norm.lean#L148-L155

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_FiniteImage
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerBMatrix_det (P : BasePrime) (r : Rank) :
    Matrix.det (cartwrightStegerBMatrix P r) =
      splittingY P r / (1 + splittingY P r) := by sorry
