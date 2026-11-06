-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityFibreDivisor_degree
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWInfinityFibreDivisor_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:04:14.049202+00:00
-- url     : https://prove2.me/theorems/15202f83-0e37-4fb0-8ddb-b5afc76a0a61
-- title:
--   F256 Garcia Stichtenoth: source Galois WInfinity Fibre Divisor degree
-- statement:
--   The weighted degree of the infinity-fibre divisor is the fibre cardinality
--   times its common inertia degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWFibreDivisors.lean#L132-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWFibreDivisors.lean#L132-L139

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWInfinityFibreDivisor_degree (m : ℕ) :
    Divisor.degree GlobalPlace.residueDegree
        (sourceGaloisWInfinityFibreDivisor m) =
      (Set.ncard (SourceGaloisWInfinityPrime m) : ℤ) *
        (sourceGaloisWInfinityInertiaDegree m : ℤ) := by sorry
