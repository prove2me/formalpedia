-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepTranslation_apply_auxiliaryCoordinate
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepTranslation_apply_auxiliaryCoordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:52:10.381609+00:00
-- url     : https://prove2.me/theorems/0bfb1534-93a5-480a-8498-20adf4f2c5c6
-- title:
--   F256 Garcia Stichtenoth: step Translation apply auxiliary Coordinate
-- statement:
--   The translation automorphism has the intended action on the source
--   auxiliary coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Translation.lean#L240-L246
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Translation.lean#L240-L246

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Translation
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepTranslation_apply_auxiliaryCoordinate
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier) :
    stepTranslation P x hx c (stepAuxiliaryCoordinate P x hx) =
      stepAuxiliaryCoordinate P x hx +
        algebraMap F256 (StepField P x hx) (c : F256) := by sorry
