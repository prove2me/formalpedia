-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosure_dz_divisor
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosure_dz_divisor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:26:10.074231+00:00
-- url     : https://prove2.me/theorems/32c82fdb-b39f-4557-b40a-9db3e52aab7d
-- title:
--   F256 Garcia Stichtenoth: source Closure dz divisor
-- statement:
--   This is the divisor of the actual nonzero dz, not a divisor defined to
--   have the desired source coefficients.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureDifferentialDivisor.lean#L47-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureDifferentialDivisor.lean#L47-L86

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureFibreDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureRegularDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferentialDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero

set_option autoImplicit false
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosure_dz_divisor (m : ℕ) :
    differentialDivisor (k := F256) (F := SourceGaloisClosureField m)
      functionFieldDifferentialGenerator functionFieldDifferentialGenerator_ne_zero =
      (16 * (sourceGaloisWZeroRamificationIndex m : ℤ) - 2) • sourceGaloisWZeroFibreDivisor m +
        (-14 * (sourceGaloisWInfinityRamificationIndex m : ℤ) - 2) •
          sourceGaloisWInfinityFibreDivisor m := by sorry
