-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepDifferentIdeal_multiplicity
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepDifferentIdeal_multiplicity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:50:39.071872+00:00
-- url     : https://prove2.me/theorems/a00c5798-dc15-4314-a57c-5068d78cf444
-- title:
--   F256 Garcia Stichtenoth: source Step Different Ideal multiplicity
-- statement:
--   The source recursion step has exact weak different exponent
--   `30 = 2 * (16 - 1)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceStep.lean#L1074-L1134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceStep.lean#L1074-L1134

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceStep
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepDifferentIdeal_multiplicity
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    multiplicity (sourceStepUpperIdeal P x hx)
        (differentIdeal P.valuationRing
          (SourceStepIntegralClosure P x hx)) = 30 := by sorry
