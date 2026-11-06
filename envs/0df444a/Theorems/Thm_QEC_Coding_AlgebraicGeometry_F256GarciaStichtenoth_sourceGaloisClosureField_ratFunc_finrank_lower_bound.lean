-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosureField_ratFunc_finrank_lower_bound
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureField_ratFunc_finrank_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:25:26.306414+00:00
-- url     : https://prove2.me/theorems/2f6aa66f-3e74-458c-9e6d-795e1ffcdc4e
-- title:
--   F256 Garcia Stichtenoth: source Galois Closure Field rat Func finrank lower bound
-- statement:
--   The corrected seed-degree growth remains a lower bound in the standard
--   function-field presentation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisFunctionField.lean#L114-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisFunctionField.lean#L114-L118

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureField_ratFunc_finrank_lower_bound (m : ℕ) :
    240 * 16 ^ m ≤
      Module.finrank (RatFunc F256) (SourceGaloisClosureField m) := by sorry
