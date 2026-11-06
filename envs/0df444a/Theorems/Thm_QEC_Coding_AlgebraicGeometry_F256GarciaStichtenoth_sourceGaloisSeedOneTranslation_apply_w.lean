-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisSeedOneTranslation_apply_w
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSeedOneTranslation_apply_w
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:12:10.959021+00:00
-- url     : https://prove2.me/theorems/3157a91c-ab07-424e-866f-fe65e6ec2509
-- title:
--   F256 Garcia Stichtenoth: source Galois Seed One Translation apply w
-- statement:
--   The lifted translation fixes the actual embedded `w` generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisSeedTranslation.lean#L220-L246
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisSeedTranslation.lean#L220-L246

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisSeedOneTranslation_apply_w (m : ℕ) :
    sourceGaloisSeedOneTranslation m
        (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) =
      (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) := by sorry
