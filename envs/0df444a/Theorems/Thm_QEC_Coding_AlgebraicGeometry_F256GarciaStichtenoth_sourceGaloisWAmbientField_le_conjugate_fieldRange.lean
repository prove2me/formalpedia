-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWAmbientField_le_conjugate_fieldRange
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWAmbientField_le_conjugate_fieldRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:45:44.702005+00:00
-- url     : https://prove2.me/theorems/1a008065-193d-4662-a6c3-1059c345d8ac
-- title:
--   F256 Garcia Stichtenoth: source Galois WAmbient Field le conjugate field Range
-- statement:
--   Consequently, the common ambient `F256(w)` field is contained in every
--   actual conjugate source field range used in the finite normal-closure
--   compositum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWNormal.lean#L194-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWNormal.lean#L194-L201

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosureFiniteCompositum
import Mathlib.FieldTheory.KummerExtension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWNormal
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open IntermediateField Polynomial

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWAmbientField_le_conjugate_fieldRange (m : ℕ)
    (f : SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureAmbient) :
    SourceGaloisWAmbientField m ≤ f.fieldRange := by sorry
