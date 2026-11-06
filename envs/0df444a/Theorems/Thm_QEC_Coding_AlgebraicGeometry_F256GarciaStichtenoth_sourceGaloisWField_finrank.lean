-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWField_finrank
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWField_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:26:06.153853+00:00
-- url     : https://prove2.me/theorems/ccd96335-4385-427f-99fb-664e580af9a3
-- title:
--   F256 Garcia Stichtenoth: source Galois WField finrank
-- statement:
--   The intermediate rational extension `F256(w) / F256(z)` has its literal
--   degree `15`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWIntermediate.lean#L64-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWIntermediate.lean#L64-L75

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisFunctionField
import Mathlib.FieldTheory.Relrank
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWIntermediate
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open IntermediateField Polynomial

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWField_finrank :
    Module.finrank GaloisBaseField SourceGaloisWField = 15 := by sorry
