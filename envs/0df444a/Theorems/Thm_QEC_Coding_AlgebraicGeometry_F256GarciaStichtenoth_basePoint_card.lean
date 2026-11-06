-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_basePoint_card
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.basePoint_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:27:39.477955+00:00
-- url     : https://prove2.me/theorems/600caa10-a6aa-4ef9-b8ef-9ce62fdb7032
-- title:
--   F256 Garcia Stichtenoth: base Point card
-- statement:
--   There are exactly 255 nonzero initial coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasePlaces.lean#L26-L27
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasePlaces.lean#L26-L27

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_FixedFieldArtinSchreier
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Mathlib.RingTheory.Polynomial.Quotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.basePoint_card : Fintype.card BasePoint = 255 := by sorry
