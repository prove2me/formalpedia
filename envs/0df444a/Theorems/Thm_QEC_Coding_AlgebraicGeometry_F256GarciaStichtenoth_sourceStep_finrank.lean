-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStep_finrank
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStep_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:48:25.708565+00:00
-- url     : https://prove2.me/theorems/d99f95ad-6ccd-469e-ac1f-4fd7a93b9c7d
-- title:
--   F256 Garcia Stichtenoth: source Step finrank
-- statement:
--   The actual source step has degree sixteen.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceStep.lean#L410-L419
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceStep.lean#L410-L419

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStep_finrank
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Module.finrank K (SourceStepField P x hx) = 16 := by sorry
