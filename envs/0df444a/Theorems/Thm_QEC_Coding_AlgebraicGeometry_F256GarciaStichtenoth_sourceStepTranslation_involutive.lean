-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepTranslation_involutive
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepTranslation_involutive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:03:07.806488+00:00
-- url     : https://prove2.me/theorems/c99f7443-4ce4-4fdd-b5e5-0bc063ed58f1
-- title:
--   F256 Garcia Stichtenoth: source Step Translation involutive
-- statement:
--   Every source-coordinate translation is involutive in characteristic
--   two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisStep.lean#L243-L251
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisStep.lean#L243-L251

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceStep
import Mathlib.FieldTheory.Galois.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisStep
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepTranslation_involutive
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (c : LinearMap.ker f256ArtinSchreier)
    (y : SourceStepField P x hx) :
    sourceStepTranslation P x hx c (sourceStepTranslation P x hx c y) = y := by sorry
