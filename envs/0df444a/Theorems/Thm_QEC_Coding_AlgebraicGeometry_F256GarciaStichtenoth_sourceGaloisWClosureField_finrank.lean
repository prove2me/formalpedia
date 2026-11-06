-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWClosureField_finrank
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureField_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:26:50.159248+00:00
-- url     : https://prove2.me/theorems/9366335e-d892-4b91-a5c4-ccaf46370369
-- title:
--   F256 Garcia Stichtenoth: source Galois WClosure Field finrank
-- statement:
--   Embedding the intermediate field into the closure preserves its degree
--   fifteen over `F256(z)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWIntermediate.lean#L114-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWIntermediate.lean#L114-L122

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisFunctionField
import Mathlib.FieldTheory.Relrank
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWIntermediate
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open IntermediateField Polynomial

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureField_finrank (m : ℕ) :
    Module.finrank GaloisBaseField (SourceGaloisWClosureField m) = 15 := by sorry
