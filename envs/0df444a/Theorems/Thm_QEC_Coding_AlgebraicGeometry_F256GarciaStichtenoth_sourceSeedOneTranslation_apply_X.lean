-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSeedOneTranslation_apply_X
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedOneTranslation_apply_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:12:20.492404+00:00
-- url     : https://prove2.me/theorems/6e98db7c-5caa-48bf-982a-3c5e2c25e243
-- title:
--   F256 Garcia Stichtenoth: source Seed One Translation apply X
-- statement:
--   The fixed-base seed translation has its literal action on `x₀`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisSeedTranslation.lean#L155-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisSeedTranslation.lean#L155-L157

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedOneTranslation_apply_X :
    sourceSeedOneTranslation RatFunc.X = RatFunc.X + 1 := by sorry
