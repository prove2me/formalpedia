-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosureSelectedDivisor_support
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSelectedDivisor_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:24:39.518202+00:00
-- url     : https://prove2.me/theorems/f305aa25-6083-48ea-9147-e7364d7ceaca
-- title:
--   F256 Garcia Stichtenoth: source Galois Closure Selected Divisor support
-- statement:
--   The support of the selected divisor is exactly the enumerated split
--   fibre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisSelectedDivisor.lean#L86-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisSelectedDivisor.lean#L86-L91

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureSelectedDivisor_support (m : ℕ) :
    ↑(sourceGaloisClosureSelectedDivisor m).support =
      Set.range (fun j : Fin (sourceGaloisClosureSelectedLength m) =>
        (sourceGaloisClosureSelectedRationalPlace m j).place) := by sorry
