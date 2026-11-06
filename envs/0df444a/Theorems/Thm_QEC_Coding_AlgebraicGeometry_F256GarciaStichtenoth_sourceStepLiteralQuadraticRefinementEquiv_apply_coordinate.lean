-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepLiteralQuadraticRefinementEquiv_apply_coordinate
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepLiteralQuadraticRefinementEquiv_apply_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:05:30.94324+00:00
-- url     : https://prove2.me/theorems/6ca23572-edc0-40f9-a3ac-cd7151da8840
-- title:
--   F256 Garcia Stichtenoth: source Step Literal Quadratic Refinement Equiv apply coordinate
-- statement:
--   The F256 Garcia Stichtenoth construction uses the source Step Literal Quadratic Refinement Equiv apply coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/LiteralSourceStep.lean#L133-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/LiteralSourceStep.lean#L133-L142

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_LiteralSourceStep
set_option autoImplicit false
open Polynomial IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K E : Type*} [_root_.Field K] [_root_.Field E]
  [Algebra F256 K] [Algebra K E]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepLiteralQuadraticRefinementEquiv_apply_coordinate
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    (y : E) (hy : y ^ 16 + y = algebraMap K E (sourceStepRhs x)) :
    sourceStepLiteralQuadraticRefinementEquiv P x hx y hy
        (quadraticArtinSchreierTowerCoordinate P (sourceStepRhs x)
          (sourceStepRhs_order P x hx) 4) = AdjoinSimple.gen K y := by sorry
