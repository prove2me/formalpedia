-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisSeedOneTranslation_apply_coordinate
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSeedOneTranslation_apply_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:12:18.382702+00:00
-- url     : https://prove2.me/theorems/6d4398d0-c3ce-4b80-869d-04d80d2f4e45
-- title:
--   F256 Garcia Stichtenoth: source Galois Seed One Translation apply coordinate
-- statement:
--   The lifted translation sends the actual seed coordinate to `x₀ + 1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisSeedTranslation.lean#L192-L217
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisSeedTranslation.lean#L192-L217

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSeedTranslation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open IntermediateField Polynomial
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSeedTranslation_f256CharTwo
attribute [local instance] sourceGaloisSeedTranslation_f256CharTwo
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSeedTranslation_ratFuncCharTwo
attribute [local instance] sourceGaloisSeedTranslation_ratFuncCharTwo

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSeedOneTranslation_apply_coordinate (m : ℕ) :
    sourceGaloisSeedOneTranslation m (sourceGaloisSeedCoordinate m) =
      sourceGaloisSeedCoordinate m + 1 := by sorry
