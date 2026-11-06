-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitIntegralCoordinate_equation
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitIntegralCoordinate_equation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:00:29.391632+00:00
-- url     : https://prove2.me/theorems/d6495692-cfe2-4cc9-ba4f-ec5b1a33a805
-- title:
--   F256 Garcia Stichtenoth: source Split Integral Coordinate equation
-- statement:
--   The integral source coordinate satisfies the literal recursion over the
--   base valuation ring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitIntegralClosure.lean#L256-L270
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitIntegralClosure.lean#L256-L270

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitAlgebra
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitIntegralClosure
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitIntegralCoordinate_equation
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    sourceSplitIntegralCoordinate Q P x hx hregular hsplit ^ 16 +
        sourceSplitIntegralCoordinate Q P x hx hregular hsplit =
      algebraMap Q.place.valuationRing
        (SourceSplitIntegralClosure Q P x hx)
        (sourceSplitBaseRhs Q x hregular hsplit) := by sorry
