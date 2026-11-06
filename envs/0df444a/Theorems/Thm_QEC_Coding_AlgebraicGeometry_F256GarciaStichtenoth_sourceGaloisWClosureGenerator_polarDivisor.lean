-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWClosureGenerator_polarDivisor
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureGenerator_polarDivisor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:15:00.798221+00:00
-- url     : https://prove2.me/theorems/fe17f22d-03c5-45d8-957c-3c943b194dd3
-- title:
--   F256 Garcia Stichtenoth: source Galois WClosure Generator polar Divisor
-- statement:
--   The pole divisor of the embedded generator is exactly its actual
--   infinity fibre, weighted by the common ramification index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWPrincipalDivisor.lean#L428-L449
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWPrincipalDivisor.lean#L428-L449

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureGenerator_polarDivisor (m : ℕ) :
    sourceGaloisWClosureGeneratorPoleDivisor m =
      sourceGaloisWInfinityRamificationIndex m •
        sourceGaloisWInfinityFibreDivisor m := by sorry
