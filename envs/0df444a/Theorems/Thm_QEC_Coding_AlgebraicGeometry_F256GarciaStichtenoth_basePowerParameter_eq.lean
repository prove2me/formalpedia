-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_basePowerParameter_eq
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.basePowerParameter_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:18:32.547429+00:00
-- url     : https://prove2.me/theorems/ed1a3aea-46e7-475c-99ed-1637c24dea36
-- title:
--   F256 Garcia Stichtenoth: base Power Parameter eq
-- statement:
--   The F256 Garcia Stichtenoth construction uses the base Power Parameter eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BaseParameter.lean#L94-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BaseParameter.lean#L94-L97

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.basePowerParameter_eq (m : ℕ) :
    basePowerParameter m =
      GlobalPlace.chartVariable (k := F256) (F := Field m) ^ 17 := by sorry
