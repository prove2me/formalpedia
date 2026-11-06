-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierIntegralRoot_multiplicity
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierIntegralRoot_multiplicity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:49:18.616495+00:00
-- url     : https://prove2.me/theorems/82fd5dc7-f2de-4298-ab2e-ea3f174e24ba
-- title:
--   F256 Garcia Stichtenoth: quadratic Artin Schreier Integral Root multiplicity
-- statement:
--   The F256 Garcia Stichtenoth construction uses the quadratic Artin Schreier Integral Root multiplicity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStepDifferent.lean#L380-L411
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStepDifferent.lean#L380-L411

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierIntegralRoot_multiplicity
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    multiplicity (quadraticArtinSchreierUpperIdeal P a ha)
      (Ideal.span
        ({quadraticArtinSchreierIntegralRoot P a ha} :
          Set (QuadraticArtinSchreierIntegralClosure P a ha))) = 1 := by sorry
