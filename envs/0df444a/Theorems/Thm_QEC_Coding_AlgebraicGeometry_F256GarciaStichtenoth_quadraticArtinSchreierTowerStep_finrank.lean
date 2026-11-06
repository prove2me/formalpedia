-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierTowerStep_finrank
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierTowerStep_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:00:21.776168+00:00
-- url     : https://prove2.me/theorems/0e680c41-2801-4f48-b9a4-6451b41e5bb3
-- title:
--   F256 Garcia Stichtenoth: quadratic Artin Schreier Tower Step finrank
-- statement:
--   Every successor in the refinement has degree two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticTower.lean#L154-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticTower.lean#L154-L162

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticTower
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
universe u
variable {K : Type u} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierTowerStep_finrank
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    Module.finrank
      (QuadraticArtinSchreierTowerField P a ha i)
      (QuadraticArtinSchreierTowerField P a ha (i + 1)) = 2 := by sorry
