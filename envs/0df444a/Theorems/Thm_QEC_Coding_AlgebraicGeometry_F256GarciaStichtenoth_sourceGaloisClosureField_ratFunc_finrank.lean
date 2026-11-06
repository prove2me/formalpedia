-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosureField_ratFunc_finrank
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureField_ratFunc_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:25:00.161077+00:00
-- url     : https://prove2.me/theorems/d5118e81-58c0-4ceb-8043-d054e02108b9
-- title:
--   F256 Garcia Stichtenoth: source Galois Closure Field rat Func finrank
-- statement:
--   The fixed-base and rational-function presentations have the same closure
--   degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisFunctionField.lean#L101-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisFunctionField.lean#L101-L110

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureField_ratFunc_finrank (m : ℕ) :
    Module.finrank (RatFunc F256) (SourceGaloisClosureField m) =
      Module.finrank GaloisBaseField (SourceGaloisClosureField m) := by sorry
