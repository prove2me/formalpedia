-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosureSelectedVanishingFunction_eq
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSelectedVanishingFunction_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:24:00.970435+00:00
-- url     : https://prove2.me/theorems/56089d7e-9dba-4266-9a4f-8c64b3a54a5f
-- title:
--   F256 Garcia Stichtenoth: source Galois Closure Selected Vanishing Function eq
-- statement:
--   The F256 Garcia Stichtenoth construction uses the source Galois Closure Selected Vanishing Function eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisSelectedDivisor.lean#L126-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisSelectedDivisor.lean#L126-L129

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_FinitePlaceDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedDivisor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open IntermediateField
open scoped BigOperators Polynomial RatFunc
noncomputable section
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_closurePolynomialAlgebra
attribute [local instance] sourceGaloisSelectedDivisor_closurePolynomialAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_closurePolynomialRatFuncScalarTower
attribute [local instance] sourceGaloisSelectedDivisor_closurePolynomialRatFuncScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSelectedDivisor_closureRatFuncIsSeparable
attribute [local instance] sourceGaloisSelectedDivisor_closureRatFuncIsSeparable

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSelectedVanishingFunction_eq (m : ℕ) :
    sourceGaloisClosureSelectedVanishingFunction m =
      ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisSelectedDivisor_E m) ^ 15 - 1 := by sorry
