-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothFunctionFieldGenus_eq
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothFunctionFieldGenus_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:38:46.41636+00:00
-- url     : https://prove2.me/theorems/a84e8e23-1c9f-4b33-8855-358358257a7d
-- title:
--   F256 Garcia Stichtenoth: f256 Garcia Stichtenoth Function Field Genus eq
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Garcia Stichtenoth Function Field Genus eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ExplicitGarciaStichtenothTower.lean#L255-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ExplicitGarciaStichtenothTower.lean#L255-L257

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothFunctionFieldGenus_eq (i : ℕ) :
    GlobalPlace.functionFieldGenus F256 (f256GarciaStichtenothField i) =
      f256GarciaStichtenothGenus i := by sorry
