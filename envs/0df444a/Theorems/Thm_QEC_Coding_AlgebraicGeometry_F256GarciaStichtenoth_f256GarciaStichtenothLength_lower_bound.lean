-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothLength_lower_bound
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothLength_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:38:28.904213+00:00
-- url     : https://prove2.me/theorems/2b34734f-9c5a-48d6-804b-63ee80df93ce
-- title:
--   F256 Garcia Stichtenoth: f256 Garcia Stichtenoth Length lower bound
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Garcia Stichtenoth Length lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ExplicitGarciaStichtenothTower.lean#L78-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ExplicitGarciaStichtenothTower.lean#L78-L80

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothLength_lower_bound (i : ℕ) :
    240 * 16 ^ (i + 2) ≤ f256GarciaStichtenothLength i := by sorry
