-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepLiteral_adjoin_finrank
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepLiteral_adjoin_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:05:28.481206+00:00
-- url     : https://prove2.me/theorems/76615af5-b74c-459d-ae00-747afa1e7622
-- title:
--   F256 Garcia Stichtenoth: source Step Literal adjoin finrank
-- statement:
--   The degree of the literal basic projection is derived, not an input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/LiteralSourceStep.lean#L117-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/LiteralSourceStep.lean#L117-L122

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_LiteralSourceStep
set_option autoImplicit false
open Polynomial IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K E : Type*} [_root_.Field K] [_root_.Field E]
  [Algebra F256 K] [Algebra K E]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepLiteral_adjoin_finrank
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (y : E) (hy : y ^ 16 + y = algebraMap K E (sourceStepRhs x)) :
    Module.finrank K K⟮y⟯ = 16 := by sorry
