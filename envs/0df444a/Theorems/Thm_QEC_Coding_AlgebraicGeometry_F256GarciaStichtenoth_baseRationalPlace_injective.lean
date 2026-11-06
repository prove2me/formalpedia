-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_baseRationalPlace_injective
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.baseRationalPlace_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:27:36.946447+00:00
-- url     : https://prove2.me/theorems/8c853344-4cf9-4234-8acb-83b17ba58c65
-- title:
--   F256 Garcia Stichtenoth: base Rational Place injective
-- statement:
--   Distinct nonzero constants give distinct selected base places.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasePlaces.lean#L259-L279
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasePlaces.lean#L259-L279

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_FixedFieldArtinSchreier
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Mathlib.RingTheory.Polynomial.Quotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.baseRationalPlace_injective :
    Function.Injective (fun a : BasePoint => (baseRationalPlace a).place) := by sorry
