-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_eq_prod_roots
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_eq_prod_roots
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:53:47.028921+00:00
-- url     : https://prove2.me/theorems/1b3e9610-56b7-4fa0-a193-e45b9cd90905
-- title:
--   F256 Garcia Stichtenoth: step Auxiliary Polynomial eq prod roots
-- statement:
--   Literal factorization of the residual auxiliary polynomial by its sixteen
--   distinct roots.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ResidualPolynomial.lean#L41-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ResidualPolynomial.lean#L41-L46

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AuxiliaryMinpoly
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ResidualPolynomial
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_eq_prod_roots (a : F256) :
    stepAuxiliaryPolynomial a =
      ∏ b ∈ f256ArtinSchreierRoots a, (X - C b) := by sorry
