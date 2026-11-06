-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_polarDivisor_basePowerParameter_degree
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.polarDivisor_basePowerParameter_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:18:50.359197+00:00
-- url     : https://prove2.me/theorems/3253f4d8-544e-476a-9ccd-52b363eaa567
-- title:
--   F256 Garcia Stichtenoth: polar Divisor base Power Parameter degree
-- statement:
--   The base power parameter has pole degree `17 * 16^m`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BaseParameter.lean#L168-L191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BaseParameter.lean#L168-L191

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Divisors
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BaseParameter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [-instance]
  selectedFieldField
  selectedFieldConstantAlgebra
  selectedFieldRatFuncAlgebra
  selectedFieldConstantTower
  selectedFieldFunctionField
  selectedFieldRatFuncSeparable
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.basePowerParameterConstantAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.basePowerParameterRatFuncAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.basePowerParameterFunctionField
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.basePowerParameterSeparable

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.polarDivisor_basePowerParameter_degree (m : ℕ) :
    Divisor.degree (basePowerParameterResidueDegree m)
        (basePowerParameterPoleDivisor m) =
      (17 * 16 ^ m : ℕ) := by sorry
