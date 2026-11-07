-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothGenus_ngu24_identity
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothGenus_ngu24_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:01:47.842945+00:00
-- url     : https://prove2.me/theorems/ea39d93c-39ea-48ac-8e95-2017991dda6b
-- title:
--   F256 Garcia Stichtenoth: f256 Garcia Stichtenoth Genus ngu24 identity
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Garcia Stichtenoth Genus ngu24 identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ExplicitGarciaStichtenothTower.lean#L264-L280
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ExplicitGarciaStichtenothTower.lean#L264-L280

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothGenus_ngu24_identity (i : ℕ) :
    15 * (f256GarciaStichtenothAlpha i : ℤ) * f256GarciaStichtenothBeta i *
      ((f256GarciaStichtenothGenus i : ℤ) - 1) =
      f256GarciaStichtenothLength i * ((f256GarciaStichtenothAlpha i : ℤ) *
        f256GarciaStichtenothBeta i - f256GarciaStichtenothAlpha i - f256GarciaStichtenothBeta i) := by sorry
