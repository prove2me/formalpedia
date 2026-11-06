-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepRhs_evaluateRegular
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepRhs_evaluateRegular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:00:42.035663+00:00
-- url     : https://prove2.me/theorems/db56efd3-f387-405b-8967-b6a930836847
-- title:
--   F256 Garcia Stichtenoth: source Step Rhs evaluate Regular
-- statement:
--   Rational-place evaluation commutes with the regular source recursion
--   right-hand side.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitIntegralClosure.lean#L164-L198
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitIntegralClosure.lean#L164-L198

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitAlgebra
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitIntegralClosure
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepRhs_evaluateRegular
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    Q.evaluateRegular (sourceStepRhs x)
        (sourceStepRhs_regularAt_of_splitValue Q x hregular hsplit) =
      sourceStepRhs (Q.evaluateRegular x hregular) := by sorry
