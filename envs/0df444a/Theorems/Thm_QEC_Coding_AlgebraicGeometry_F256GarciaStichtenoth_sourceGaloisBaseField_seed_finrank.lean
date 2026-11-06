-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisBaseField_seed_finrank
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisBaseField_seed_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:23:26.856209+00:00
-- url     : https://prove2.me/theorems/7b119e49-6498-45d3-85a8-6cd30bc892b5
-- title:
--   F256 Garcia Stichtenoth: source Galois Base Field seed finrank
-- statement:
--   The corrected source seed has degree `240 * 16^m` over the fixed base.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceNormalClosure.lean#L40-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceNormalClosure.lean#L40-L49

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisSeedSeparable
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.SeparableClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosure
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisBaseField_seed_finrank (m : ℕ) :
    Module.finrank GaloisBaseField (SourceField m) = 240 * 16 ^ m := by sorry
