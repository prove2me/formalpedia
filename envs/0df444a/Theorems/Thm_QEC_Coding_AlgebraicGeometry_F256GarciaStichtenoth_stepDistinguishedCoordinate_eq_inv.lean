-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepDistinguishedCoordinate_eq_inv
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepDistinguishedCoordinate_eq_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:48:03.321353+00:00
-- url     : https://prove2.me/theorems/497f391f-4112-4730-95df-3f6a802b6d47
-- title:
--   F256 Garcia Stichtenoth: step Distinguished Coordinate eq inv
-- statement:
--   The F256 Garcia Stichtenoth construction uses the step Distinguished Coordinate eq inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Step.lean#L404-L414
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Step.lean#L404-L414

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_FixedFieldArtinSchreier
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepDistinguishedCoordinate_eq_inv
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    stepDistinguishedCoordinate P x hx = (stepReciprocalRoot P x hx)⁻¹ := by sorry
