-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_RegularQuadraticEdge_of_restrictScalars
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.RegularQuadraticEdge.of_restrictScalars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:12:32.01423+00:00
-- url     : https://prove2.me/theorems/32e8d241-6cb7-4544-a2cf-f5b961e04651
-- title:
--   Regular Quadratic Edge: of restrict Scalars
-- statement:
--   The Regular Quadratic Edge construction uses the of restrict Scalars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularRefinement.lean#L110-L120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularRefinement.lean#L110-L120

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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.RegularQuadraticEdge.of_restrictScalars
    {J L : IntermediateField B E}
    (h : RegularQuadraticEdge Q (J.restrictScalars F) (L.restrictScalars F)) :
    RegularQuadraticEdge Q J L := by sorry
