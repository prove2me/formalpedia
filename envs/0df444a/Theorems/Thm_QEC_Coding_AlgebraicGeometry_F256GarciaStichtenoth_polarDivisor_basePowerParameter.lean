-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_polarDivisor_basePowerParameter
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.polarDivisor_basePowerParameter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:18:11.549533+00:00
-- url     : https://prove2.me/theorems/01e293db-1744-4e7a-ae00-58b869c0724f
-- title:
--   F256 Garcia Stichtenoth: polar Divisor base Power Parameter
-- statement:
--   Taking the seventeenth power multiplies the chart-variable pole divisor
--   by seventeen.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BaseParameter.lean#L140-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BaseParameter.lean#L140-L165

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.polarDivisor_basePowerParameter (m : ℕ) :
    basePowerParameterPoleDivisor m =
      17 • chartVariablePoleDivisor m := by sorry
