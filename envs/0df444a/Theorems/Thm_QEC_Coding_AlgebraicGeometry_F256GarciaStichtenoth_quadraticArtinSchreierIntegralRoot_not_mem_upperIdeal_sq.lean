-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierIntegralRoot_not_mem_upperIdeal_sq
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierIntegralRoot_not_mem_upperIdeal_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:49:18.729208+00:00
-- url     : https://prove2.me/theorems/f83f1b9c-c23a-421b-8d8c-3aee464ab65f
-- title:
--   F256 Garcia Stichtenoth: quadratic Artin Schreier Integral Root not mem upper Ideal sq
-- statement:
--   The F256 Garcia Stichtenoth construction uses the quadratic Artin Schreier Integral Root not mem upper Ideal sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStepDifferent.lean#L317-L378
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStepDifferent.lean#L317-L378

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierIntegralRoot_not_mem_upperIdeal_sq
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    quadraticArtinSchreierIntegralRoot P a ha ∉
      (quadraticArtinSchreierUpperIdeal P a ha) ^ 2 := by sorry
