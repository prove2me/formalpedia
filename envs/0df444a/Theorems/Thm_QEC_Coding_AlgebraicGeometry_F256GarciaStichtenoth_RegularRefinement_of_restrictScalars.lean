-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_RegularRefinement_of_restrictScalars
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.RegularRefinement.of_restrictScalars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:18:21.424202+00:00
-- url     : https://prove2.me/theorems/094f9f34-65b4-4275-857d-a83786df6932
-- title:
--   Regular Refinement: of restrict Scalars
-- statement:
--   Read the same regular generators over a larger common base. Every
--   intermediate field contains the initial field, so none is added or guessed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularRefinement.lean#L124-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularRefinement.lean#L124-L144

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinement
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {F E : Type*} [_root_.Field F] [_root_.Field E] [Algebra F E]
  [Algebra F256 E] (Q : GlobalPlace F256 E)
variable {B : Type*} [_root_.Field B] [Algebra F B] [Algebra B E]
  [IsScalarTower F B E]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.RegularRefinement.of_restrictScalars
    {J L : IntermediateField B E}
    (h : RegularRefinement Q (J.restrictScalars F) (L.restrictScalars F)) :
    RegularRefinement Q J L := by sorry
