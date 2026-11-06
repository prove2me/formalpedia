-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreier_ramificationIdx_eq_two
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreier_ramificationIdx_eq_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:48:19.032872+00:00
-- url     : https://prove2.me/theorems/c7532543-3534-4a60-85e7-27d93ac6ddba
-- title:
--   F256 Garcia Stichtenoth: quadratic Artin Schreier ramification Idx eq two
-- statement:
--   The F256 Garcia Stichtenoth construction uses the quadratic Artin Schreier ramification Idx eq two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStepDifferent.lean#L259-L305
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStepDifferent.lean#L259-L305

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStep
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreier_ramificationIdx_eq_two
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    (IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx'
      (quadraticArtinSchreierUpperIdeal P a ha) = 2 := by sorry
