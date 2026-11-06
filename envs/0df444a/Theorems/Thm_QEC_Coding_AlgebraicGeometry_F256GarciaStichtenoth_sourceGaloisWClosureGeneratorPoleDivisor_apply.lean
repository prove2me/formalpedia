-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWClosureGeneratorPoleDivisor_apply
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureGeneratorPoleDivisor_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:15:15.507172+00:00
-- url     : https://prove2.me/theorems/2fb90f15-c087-4242-8da1-203d4149afc2
-- title:
--   F256 Garcia Stichtenoth: source Galois WClosure Generator Pole Divisor apply
-- statement:
--   The coefficient of the generator's pole divisor is the negative part of
--   its normalized order at the actual global place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWPrincipalDivisor.lean#L235-L241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWPrincipalDivisor.lean#L235-L241

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureGeneratorPoleDivisor_apply (m : ℕ)
    (P : GlobalPlace F256 (sourceGaloisWPrincipalDivisor_E m)) :
    sourceGaloisWClosureGeneratorPoleDivisor m P =
      max (-P.order
        ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisWPrincipalDivisor_E m)) 0 := by sorry
