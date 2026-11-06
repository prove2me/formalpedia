-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierTower_equation
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierTower_equation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:00:18.153353+00:00
-- url     : https://prove2.me/theorems/78829406-ce7c-4419-b504-449e34adcce8
-- title:
--   F256 Garcia Stichtenoth: quadratic Artin Schreier Tower equation
-- statement:
--   The literal quadratic equation at every successor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticTower.lean#L190-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticTower.lean#L190-L199

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticTower
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
universe u
variable {K : Type u} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierTower_equation
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    quadraticArtinSchreierTowerCoordinate P a ha (i + 1) ^ 2 +
        quadraticArtinSchreierTowerCoordinate P a ha (i + 1) =
      quadraticArtinSchreierTowerEmbedding P a ha i
        (quadraticArtinSchreierTowerCoordinate P a ha i) := by sorry
