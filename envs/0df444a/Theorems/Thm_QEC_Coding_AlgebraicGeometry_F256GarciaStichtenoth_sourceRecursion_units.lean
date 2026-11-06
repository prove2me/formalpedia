-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceRecursion_units
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceRecursion_units
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:33:37.571777+00:00
-- url     : https://prove2.me/theorems/acf57c68-d897-4e1f-affa-ca0c1228f68c
-- title:
--   F256 Garcia Stichtenoth: source Recursion units
-- statement:
--   The displayed rational recursion preserves this unit condition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceRegularCoordinates.lean#L44-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceRegularCoordinates.lean#L44-L49

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceCoordinates
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalTraceSeed
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRegularCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {E : Type*} [_root_.Field E] [Algebra F256 E]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceRecursion_units (Q : GlobalPlace F256 E) (x y : E)
    (hx : Q.valuation x = 1) (hden : Q.valuation (x ^ 15 + 1) = 1)
    (hrec : y ^ 16 + y = sourceStepRhs x) :
    Q.valuation y = 1 ∧ Q.valuation (y ^ 15 + 1) = 1 := by sorry
