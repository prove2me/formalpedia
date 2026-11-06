-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_galoisBaseField_ratFunc_finrank
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisBaseField_ratFunc_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:20:09.059233+00:00
-- url     : https://prove2.me/theorems/95369b6f-b106-41b7-ad82-d3f5a6ab0060
-- title:
--   F256 Garcia Stichtenoth: galois Base Field rat Func finrank
-- statement:
--   The rational seed extension `F256(x₀) / F256(z)` has its literal degree
--   `240 = 15 * 16`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GaloisBaseField.lean#L89-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GaloisBaseField.lean#L89-L98

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BaseParameter
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisBase
import Mathlib.FieldTheory.RatFunc.Luroth
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisBaseField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open IntermediateField Polynomial

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisBaseField_ratFunc_finrank :
    Module.finrank GaloisBaseField (RatFunc F256) = 240 := by sorry
