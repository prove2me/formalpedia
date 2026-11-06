-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWZeroRamificationIndex_mul_fibreDivisor_degree_eq_length_div
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroRamificationIndex_mul_fibreDivisor_degree_eq_length_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:04:35.702035+00:00
-- url     : https://prove2.me/theorems/1642301c-15ff-43ce-8f35-1a7d682337db
-- title:
--   F256 Garcia Stichtenoth: source Galois WZero Ramification Index mul fibre Divisor degree eq length div
-- statement:
--   The source normalization `e₀ deg(A) = n / 15` for the actual zero-fibre
--   divisor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWFibreDivisors.lean#L183-L192
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWFibreDivisors.lean#L183-L192

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWResidueDegrees
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_FinitePlaceDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWFibreDivisors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
noncomputable section
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFibreDivisors_closurePolynomialAlgebra
attribute [local instance] sourceGaloisWFibreDivisors_closurePolynomialAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFibreDivisors_closurePolynomialRatFuncScalarTower
attribute [local instance] sourceGaloisWFibreDivisors_closurePolynomialRatFuncScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFibreDivisors_closureRatFuncIsSeparable
attribute [local instance] sourceGaloisWFibreDivisors_closureRatFuncIsSeparable
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFibreDivisors_sourceGaloisWZeroPrimeFintype
attribute [local instance] sourceGaloisWFibreDivisors_sourceGaloisWZeroPrimeFintype
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFibreDivisors_sourceGaloisWInfinityPrimeFintype
attribute [local instance] sourceGaloisWFibreDivisors_sourceGaloisWInfinityPrimeFintype
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFibreDivisors_sourceGaloisWZeroPrimeNonempty
attribute [local instance] sourceGaloisWFibreDivisors_sourceGaloisWZeroPrimeNonempty
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFibreDivisors_sourceGaloisWInfinityPrimeNonempty
attribute [local instance] sourceGaloisWFibreDivisors_sourceGaloisWInfinityPrimeNonempty

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroRamificationIndex_mul_fibreDivisor_degree_eq_length_div
    (m : ℕ) :
    (sourceGaloisWZeroRamificationIndex m : ℤ) *
        Divisor.degree GlobalPlace.residueDegree
          (sourceGaloisWZeroFibreDivisor m) =
      (sourceGaloisClosureSelectedLength m / 15 : ℕ) := by sorry
