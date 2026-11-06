-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepTranslation_involutive
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepTranslation_involutive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:01:15.336311+00:00
-- url     : https://prove2.me/theorems/7dc207a6-bf64-49ad-851b-f2769143c838
-- title:
--   F256 Garcia Stichtenoth: step Translation involutive
-- statement:
--   In characteristic two every constant translation is an involution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Translation.lean#L249-L256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Translation.lean#L249-L256

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Translation
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepTranslation_involutive
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) (y : StepField P x hx) :
    stepTranslation P x hx c (stepTranslation P x hx c y) = y := by sorry
