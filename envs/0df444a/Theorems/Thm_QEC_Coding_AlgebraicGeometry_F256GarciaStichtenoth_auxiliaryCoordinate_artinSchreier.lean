-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_auxiliaryCoordinate_artinSchreier
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.auxiliaryCoordinate_artinSchreier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:07:33.774313+00:00
-- url     : https://prove2.me/theorems/1e7d7132-cee1-456a-803e-17094b062c84
-- title:
--   F256 Garcia Stichtenoth: auxiliary Coordinate artin Schreier
-- statement:
--   The literal Garcia--Stichtenoth Artin--Schreier equation at every level.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Recursion.lean#L151-L156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Recursion.lean#L151-L156

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
import Mathlib.NumberTheory.FunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Recursion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.auxiliaryCoordinate_artinSchreier (i : ℕ) :
    auxiliaryCoordinate i ^ 16 + auxiliaryCoordinate i =
      stepEmbedding i (distinguishedCoordinate i) ^ 17 := by sorry
