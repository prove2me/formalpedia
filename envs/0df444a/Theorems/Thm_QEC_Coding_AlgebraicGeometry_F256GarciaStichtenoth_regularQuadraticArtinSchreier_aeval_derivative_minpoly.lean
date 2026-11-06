-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_regularQuadraticArtinSchreier_aeval_derivative_minpoly
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.regularQuadraticArtinSchreier_aeval_derivative_minpoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:50:31.295401+00:00
-- url     : https://prove2.me/theorems/e61ea0e7-4e9d-47b4-b15c-d204f8458717
-- title:
--   F256 Garcia Stichtenoth: regular Quadratic Artin Schreier aeval derivative minpoly
-- statement:
--   The F256 Garcia Stichtenoth construction uses the regular Quadratic Artin Schreier aeval derivative minpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularQuadraticStep.lean#L437-L458
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularQuadraticStep.lean#L437-L458

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularQuadraticStep
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.regularQuadraticArtinSchreier_aeval_derivative_minpoly
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    Polynomial.aeval (regularQuadraticArtinSchreierIntegralRoot P b hirr)
        (derivative (minpoly P.valuationRing
          (regularQuadraticArtinSchreierIntegralRoot P b hirr))) = 1 := by sorry
