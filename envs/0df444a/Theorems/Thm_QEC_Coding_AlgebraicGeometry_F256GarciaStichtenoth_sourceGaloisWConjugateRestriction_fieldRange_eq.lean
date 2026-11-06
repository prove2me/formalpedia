-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWConjugateRestriction_fieldRange_eq
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWConjugateRestriction_fieldRange_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:44:57.682879+00:00
-- url     : https://prove2.me/theorems/478420b7-867b-4df3-b340-d0fcf98d63b7
-- title:
--   F256 Garcia Stichtenoth: source Galois WConjugate Restriction field Range eq
-- statement:
--   Every fixed-base embedding of source level `m` sends its literal
--   `F256(w)` subfield onto the same ambient intermediate field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWNormal.lean#L168-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWNormal.lean#L168-L189

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosureFiniteCompositum
import Mathlib.FieldTheory.KummerExtension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWNormal
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open IntermediateField Polynomial

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWConjugateRestriction_fieldRange_eq (m : ℕ)
    (f : SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureAmbient) :
    (f.comp (sourceGaloisWFieldToSource m)).fieldRange =
      SourceGaloisWAmbientField m := by sorry
