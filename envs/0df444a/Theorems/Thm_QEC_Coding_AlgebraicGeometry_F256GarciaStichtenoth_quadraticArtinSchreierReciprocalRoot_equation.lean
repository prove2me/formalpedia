-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierReciprocalRoot_equation
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierReciprocalRoot_equation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:48:10.980202+00:00
-- url     : https://prove2.me/theorems/77ae1870-e913-44a6-9cb1-310fd0773dc4
-- title:
--   F256 Garcia Stichtenoth: quadratic Artin Schreier Reciprocal Root equation
-- statement:
--   The F256 Garcia Stichtenoth construction uses the quadratic Artin Schreier Reciprocal Root equation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStep.lean#L282-L304
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStep.lean#L282-L304

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStep
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierReciprocalRoot_equation
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    quadraticArtinSchreierReciprocalRoot P a ha ^ 2 +
        quadraticArtinSchreierEmbedding P a ha a⁻¹ *
          quadraticArtinSchreierReciprocalRoot P a ha +
        quadraticArtinSchreierEmbedding P a ha a⁻¹ = 0 := by sorry
