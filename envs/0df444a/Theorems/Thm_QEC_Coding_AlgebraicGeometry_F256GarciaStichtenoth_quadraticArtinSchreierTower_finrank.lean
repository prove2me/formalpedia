-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierTower_finrank
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierTower_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:00:22.518292+00:00
-- url     : https://prove2.me/theorems/fc2bf7b4-24db-4bbe-96d9-5f950c6aaf89
-- title:
--   F256 Garcia Stichtenoth: quadratic Artin Schreier Tower finrank
-- statement:
--   Level `i` has degree `2^i` over the starting field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticTower.lean#L165-L187
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticTower.lean#L165-L187

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticTower
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
universe u
variable {K : Type u} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierTower_finrank
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    Module.finrank K (QuadraticArtinSchreierTowerField P a ha i) = 2 ^ i := by sorry
