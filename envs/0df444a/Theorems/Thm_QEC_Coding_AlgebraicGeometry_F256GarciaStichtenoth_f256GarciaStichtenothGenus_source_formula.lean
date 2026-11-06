-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothGenus_source_formula
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothGenus_source_formula
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:40:48.016314+00:00
-- url     : https://prove2.me/theorems/6778dae3-16f8-4dc6-8a33-39989cd527ca
-- title:
--   F256 Garcia Stichtenoth: f256 Garcia Stichtenoth Genus source formula
-- statement:
--   The F256 Garcia Stichtenoth construction uses the f256 Garcia Stichtenoth Genus source formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ExplicitGarciaStichtenothTower.lean#L259-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ExplicitGarciaStichtenothTower.lean#L259-L262

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothGenus_source_formula (i : ℕ) :
    (f256GarciaStichtenothGenus i : ℚ) = 1 + (f256GarciaStichtenothLength i : ℚ) / 15 *
      (1 - 1 / (f256GarciaStichtenothAlpha i : ℚ) - 1 / (f256GarciaStichtenothBeta i : ℚ)) := by sorry
