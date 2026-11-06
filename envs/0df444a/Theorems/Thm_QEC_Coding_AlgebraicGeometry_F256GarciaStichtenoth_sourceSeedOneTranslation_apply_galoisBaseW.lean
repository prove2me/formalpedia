-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSeedOneTranslation_apply_galoisBaseW
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedOneTranslation_apply_galoisBaseW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:12:14.686176+00:00
-- url     : https://prove2.me/theorems/ad32c2fb-c3b6-4969-83a1-042c13ddbb2e
-- title:
--   F256 Garcia Stichtenoth: source Seed One Translation apply galois Base W
-- statement:
--   The seed translation fixes `w = x₀^16 + x₀`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisSeedTranslation.lean#L160-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisSeedTranslation.lean#L160-L162

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedOneTranslation_apply_galoisBaseW :
    sourceSeedOneTranslation galoisBaseW = galoisBaseW := by sorry
