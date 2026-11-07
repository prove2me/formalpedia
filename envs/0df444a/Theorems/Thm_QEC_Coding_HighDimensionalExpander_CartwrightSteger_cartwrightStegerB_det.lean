-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerB_det
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerB_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:42:45.852529+00:00
-- url     : https://prove2.me/theorems/ef006468-77f3-441a-98fa-401b55ec2ea1
-- title:
--   Cartwright Steger: cartwright Steger B det
-- statement:
--   Unit-valued version of LSV Proposition `normb`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/Norm.lean#L170-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Norm/Norm.lean#L170-L174

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_FiniteImage
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerB_det (P : BasePrime) (r : Rank) :
    Matrix.GeneralLinearGroup.det (cartwrightStegerB P r) =
      cartwrightStegerNormUnit P r := by sorry
