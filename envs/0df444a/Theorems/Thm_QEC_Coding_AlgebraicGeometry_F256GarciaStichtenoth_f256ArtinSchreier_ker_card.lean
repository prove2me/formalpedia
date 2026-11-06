-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ArtinSchreier_ker_card
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ArtinSchreier_ker_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:44:16.729197+00:00
-- url     : https://prove2.me/theorems/aefb527d-8305-4fcc-b16b-2e01135c5131
-- title:
--   F256 Garcia Stichtenoth: f256 Artin Schreier ker card
-- statement:
--   The additive kernel contains exactly sixteen constants.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/FixedFieldArtinSchreier.lean#L89-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/FixedFieldArtinSchreier.lean#L89-L93

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Field
import Mathlib.FieldTheory.Finite.Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_FixedFieldArtinSchreier
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ArtinSchreier_ker_card :
    Fintype.card (LinearMap.ker f256ArtinSchreier) = 16 := by sorry
