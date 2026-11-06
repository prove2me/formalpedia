-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceSplitIntegralCoordinate
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceSplitIntegralCoordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:00:34.071651+00:00
-- url     : https://prove2.me/theorems/c283696d-9872-4a9f-a7e4-3a98cf233a0c
-- title:
--   F256 Garcia Stichtenoth: coe source Split Integral Coordinate
-- statement:
--   The F256 Garcia Stichtenoth construction uses the coe source Split Integral Coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitIntegralClosure.lean#L245-L252
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitIntegralClosure.lean#L245-L252

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitAlgebra
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitIntegralClosure
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceSplitIntegralCoordinate
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    (sourceSplitIntegralCoordinate Q P x hx hregular hsplit :
        SourceStepField P x hx) = sourceStepCoordinate P x hx := by sorry

attribute [defeq] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceSplitIntegralCoordinate
