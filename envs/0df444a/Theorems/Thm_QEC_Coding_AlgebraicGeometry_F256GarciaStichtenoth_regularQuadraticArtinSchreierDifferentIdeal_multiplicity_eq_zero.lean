-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_regularQuadraticArtinSchreierDifferentIdeal_multiplicity_eq_zero
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.regularQuadraticArtinSchreierDifferentIdeal_multiplicity_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:51:58.605358+00:00
-- url     : https://prove2.me/theorems/d3fd4a43-866b-4e33-ae99-ef3d92a9f5ee
-- title:
--   F256 Garcia Stichtenoth: regular Quadratic Artin Schreier Different Ideal multiplicity eq zero
-- statement:
--   Every chosen upper prime has relative different exponent zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularQuadraticStep.lean#L547-L558
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularQuadraticStep.lean#L547-L558

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularQuadraticStep
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.regularQuadraticArtinSchreierDifferentIdeal_multiplicity_eq_zero
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    multiplicity (regularQuadraticArtinSchreierUpperIdeal P b hirr)
        (differentIdeal P.valuationRing
          (RegularQuadraticArtinSchreierIntegralClosure P b hirr)) = 0 := by sorry
