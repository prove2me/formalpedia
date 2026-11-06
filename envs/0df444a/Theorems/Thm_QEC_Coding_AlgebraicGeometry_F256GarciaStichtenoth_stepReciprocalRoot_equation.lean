-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepReciprocalRoot_equation
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepReciprocalRoot_equation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:47:58.996343+00:00
-- url     : https://prove2.me/theorems/330fa14e-4fc5-4522-b4d3-db494d442290
-- title:
--   F256 Garcia Stichtenoth: step Reciprocal Root equation
-- statement:
--   The reciprocal-root equation in the degree-sixteen step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Step.lean#L334-L357
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Step.lean#L334-L357

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepReciprocalRoot_equation (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    stepReciprocalRoot P x hx ^ 16 +
        stepFieldEmbedding P x hx (x⁻¹ ^ 16) * stepReciprocalRoot P x hx ^ 15 +
        stepFieldEmbedding P x hx x⁻¹ = 0 := by sorry
