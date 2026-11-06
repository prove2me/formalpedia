-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreier_finrank
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreier_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:48:01.960772+00:00
-- url     : https://prove2.me/theorems/c2e2c3e6-0144-4b64-acd0-26fc0644c2b0
-- title:
--   F256 Garcia Stichtenoth: quadratic Artin Schreier finrank
-- statement:
--   The constructed quadratic Artin--Schreier step has degree two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStep.lean#L344-L353
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStep.lean#L344-L353

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStep
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreier_finrank
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    Module.finrank K (QuadraticArtinSchreierField P a ha) = 2 := by sorry
