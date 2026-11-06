-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_splitIntegralAuxiliaryCoordinate_equation
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitIntegralAuxiliaryCoordinate_equation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:58:24.787549+00:00
-- url     : https://prove2.me/theorems/cf487aec-151c-499b-9ef4-f6c0c09f99a1
-- title:
--   F256 Garcia Stichtenoth: split Integral Auxiliary Coordinate equation
-- statement:
--   The integral auxiliary coordinate satisfies the source recursion over the
--   base valuation ring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SplitIntegralClosure.lean#L155-L169
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SplitIntegralClosure.lean#L155-L169

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ResidualPolynomial
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitIntegralClosure
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitIntegralAuxiliaryCoordinate_equation
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    splitIntegralAuxiliaryCoordinate Q P x hx hregular ^ 16 +
        splitIntegralAuxiliaryCoordinate Q P x hx hregular =
      algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
        ((splitBaseCoordinate Q x hregular) ^ 17) := by sorry
