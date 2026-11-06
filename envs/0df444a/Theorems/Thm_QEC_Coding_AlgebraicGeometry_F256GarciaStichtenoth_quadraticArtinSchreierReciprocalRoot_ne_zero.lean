-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierReciprocalRoot_ne_zero
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierReciprocalRoot_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:48:01.172623+00:00
-- url     : https://prove2.me/theorems/685c89e9-bd65-42ea-b5f3-08abdfe138f6
-- title:
--   F256 Garcia Stichtenoth: quadratic Artin Schreier Reciprocal Root ne zero
-- statement:
--   The F256 Garcia Stichtenoth construction uses the quadratic Artin Schreier Reciprocal Root ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStep.lean#L253-L280
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStep.lean#L253-L280

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStep
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierReciprocalRoot_ne_zero
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    quadraticArtinSchreierReciprocalRoot P a ha ≠ 0 := by sorry
