-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothAlpha_two_le
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothAlpha_two_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:38:35.807464+00:00
-- url     : https://prove2.me/theorems/eebb6380-f36d-44cc-972d-2f38cb6a3313
-- title:
--   F256 Garcia Stichtenoth: f256 Garcia Stichtenoth Alpha two le
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Garcia Stichtenoth Alpha two le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ExplicitGarciaStichtenothTower.lean#L177-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ExplicitGarciaStichtenothTower.lean#L177-L178

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureGenus
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedFibreSeparation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWZeroRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter FunctionFieldDifferential
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothAlpha_two_le (i : ℕ) : 2 ≤ f256GarciaStichtenothAlpha i := by sorry
