-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_polarDivisor_basePowerParameter_degree_selectedLevel
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.polarDivisor_basePowerParameter_degree_selectedLevel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:18:24.70858+00:00
-- url     : https://prove2.me/theorems/0ef4ac23-140d-4bc9-b5fe-b2e39fc7827e
-- title:
--   F256 Garcia Stichtenoth: polar Divisor base Power Parameter degree selected Level
-- statement:
--   For the original-family tail `Field (i + 2)`, the pole degree of `X^17`
--   equals `selectedLength i / 15`. This arithmetic identity does not identify
--   the fibre divisors of the source normal-closure family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BaseParameter.lean#L196-L214
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BaseParameter.lean#L196-L214

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.polarDivisor_basePowerParameter_degree_selectedLevel (i : ℕ) :
    Divisor.degree (basePowerParameterResidueDegree (i + 2))
        (basePowerParameterPoleDivisor (i + 2)) =
      ((selectedLength i / 15 : ℕ) : ℤ) := by sorry
