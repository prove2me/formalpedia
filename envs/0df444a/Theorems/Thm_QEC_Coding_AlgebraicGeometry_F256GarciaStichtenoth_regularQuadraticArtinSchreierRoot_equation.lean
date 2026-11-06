-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_regularQuadraticArtinSchreierRoot_equation
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.regularQuadraticArtinSchreierRoot_equation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:51:40.662193+00:00
-- url     : https://prove2.me/theorems/b29e08bf-1b6a-45b2-bb05-3605d046f404
-- title:
--   F256 Garcia Stichtenoth: regular Quadratic Artin Schreier Root equation
-- statement:
--   The constructed root satisfies the literal regular Artin--Schreier
--   equation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularQuadraticStep.lean#L153-L197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularQuadraticStep.lean#L153-L197

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularQuadraticStep
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.regularQuadraticArtinSchreierRoot_equation
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    regularQuadraticArtinSchreierRoot P b hirr ^ 2 +
        regularQuadraticArtinSchreierRoot P b hirr =
      regularQuadraticArtinSchreierEmbedding P b hirr (b : K) := by sorry
