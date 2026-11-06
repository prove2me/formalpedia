-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ArtinSchreier_ker_finrank
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ArtinSchreier_ker_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:44:22.247556+00:00
-- url     : https://prove2.me/theorems/8ebe7b70-3333-4cb7-933e-284cf5f9e752
-- title:
--   F256 Garcia Stichtenoth: f256 Artin Schreier ker finrank
-- statement:
--   The additive kernel has relative dimension one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/FixedFieldArtinSchreier.lean#L78-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/FixedFieldArtinSchreier.lean#L78-L86

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Field
import Mathlib.FieldTheory.Finite.Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_FixedFieldArtinSchreier
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ArtinSchreier_ker_finrank :
    Module.finrank F16 (LinearMap.ker f256ArtinSchreier) = 1 := by sorry
