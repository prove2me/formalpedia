-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWClosureGenerator_principalDivisor
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureGenerator_principalDivisor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:17:55.574872+00:00
-- url     : https://prove2.me/theorems/66d22f62-6b47-4383-8a73-8dba0a8b5c62
-- title:
--   F256 Garcia Stichtenoth: source Galois WClosure Generator principal Divisor
-- statement:
--   The actual principal divisor of `w` is its ramification-weighted zero
--   fibre minus its ramification-weighted infinity fibre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWPrincipalDivisor.lean#L533-L559
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWPrincipalDivisor.lean#L533-L559

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWFibreDivisors
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPrincipalDivisor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open IntermediateField
open scoped Polynomial RatFunc
noncomputable section
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPrincipalDivisor_closurePolynomialAlgebra
attribute [local instance] sourceGaloisWPrincipalDivisor_closurePolynomialAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPrincipalDivisor_closurePolynomialRatFuncScalarTower
attribute [local instance] sourceGaloisWPrincipalDivisor_closurePolynomialRatFuncScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWPrincipalDivisor_closureRatFuncIsSeparable
attribute [local instance] sourceGaloisWPrincipalDivisor_closureRatFuncIsSeparable

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureGenerator_principalDivisor (m : ℕ) :
    GlobalPlace.principalDivisor (k := F256) (F := sourceGaloisWPrincipalDivisor_E m)
        (Units.mk0
          ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisWPrincipalDivisor_E m)
          (sourceGaloisWClosureGenerator_ne_zero m)) =
      sourceGaloisWZeroRamificationIndex m • sourceGaloisWZeroFibreDivisor m -
        sourceGaloisWInfinityRamificationIndex m •
          sourceGaloisWInfinityFibreDivisor m := by sorry
