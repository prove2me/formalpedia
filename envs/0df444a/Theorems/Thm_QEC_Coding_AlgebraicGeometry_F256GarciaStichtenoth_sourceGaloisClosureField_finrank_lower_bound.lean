-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosureField_finrank_lower_bound
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureField_finrank_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:23:23.374057+00:00
-- url     : https://prove2.me/theorems/dbe949de-c019-4f7e-abfc-ec38844116e6
-- title:
--   F256 Garcia Stichtenoth: source Galois Closure Field finrank lower bound
-- statement:
--   The actual normal-closure degree dominates the proved corrected-seed
--   degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceNormalClosure.lean#L140-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceNormalClosure.lean#L140-L146

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisSeedSeparable
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.SeparableClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosure
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureField_finrank_lower_bound (m : ℕ) :
    240 * 16 ^ m ≤
      Module.finrank GaloisBaseField (SourceGaloisClosureField m) := by sorry
