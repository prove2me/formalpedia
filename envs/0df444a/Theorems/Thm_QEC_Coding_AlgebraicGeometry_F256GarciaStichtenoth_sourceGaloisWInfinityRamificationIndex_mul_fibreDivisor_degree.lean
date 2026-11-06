-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityRamificationIndex_mul_fibreDivisor_degree
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWInfinityRamificationIndex_mul_fibreDivisor_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:04:47.376725+00:00
-- url     : https://prove2.me/theorems/c8ca205b-d906-4b86-aaec-0a5755fd0475
-- title:
--   F256 Garcia Stichtenoth: source Galois WInfinity Ramification Index mul fibre Divisor degree
-- statement:
--   The infinity-fibre ramification index times its divisor degree is the
--   actual relative source-normal-closure degree over `F256(w)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWFibreDivisors.lean#L163-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWFibreDivisors.lean#L163-L179

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWInfinityRamificationIndex_mul_fibreDivisor_degree (m : ℕ) :
    (sourceGaloisWInfinityRamificationIndex m : ℤ) *
        Divisor.degree GlobalPlace.residueDegree
          (sourceGaloisWInfinityFibreDivisor m) =
      (sourceGaloisWRelativeDegree m : ℤ) := by sorry
