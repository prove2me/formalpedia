-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepQuadraticRefinementEquiv_apply_coordinate
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepQuadraticRefinementEquiv_apply_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:04:38.165197+00:00
-- url     : https://prove2.me/theorems/dca8fbf4-f1e2-4161-a05c-aac2d1aacf1c
-- title:
--   F256 Garcia Stichtenoth: source Step Quadratic Refinement Equiv apply coordinate
-- statement:
--   The field equivalence sends the source coordinate to the terminal
--   quadratic-refinement coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticRefinement.lean#L225-L233
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticRefinement.lean#L225-L233

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticRefinement
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
universe u
variable {K : Type u} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepQuadraticRefinementEquiv_apply_coordinate
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepQuadraticRefinementEquiv P x hx
        (sourceStepCoordinate P x hx) =
      quadraticArtinSchreierTowerCoordinate P (sourceStepRhs x)
        (sourceStepRhs_order P x hx) 4 := by sorry
