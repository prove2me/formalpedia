-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierCoordinate_equation
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierCoordinate_equation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:49:18.796209+00:00
-- url     : https://prove2.me/theorems/3accf019-0faa-4be8-b26d-c5815b2a311c
-- title:
--   F256 Garcia Stichtenoth: quadratic Artin Schreier Coordinate equation
-- statement:
--   The constructed coordinate satisfies `y² + y = a`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStep.lean#L313-L341
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStep.lean#L313-L341

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStep
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierCoordinate_equation
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    quadraticArtinSchreierCoordinate P a ha ^ 2 +
        quadraticArtinSchreierCoordinate P a ha =
      quadraticArtinSchreierEmbedding P a ha a := by sorry
