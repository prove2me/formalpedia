-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_exists_eq_algebraMap_of_stepAuxiliaryPolynomial_aeval_eq_zero
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.exists_eq_algebraMap_of_stepAuxiliaryPolynomial_aeval_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:53:34.5662+00:00
-- url     : https://prove2.me/theorems/16ea9f92-7fec-4487-952d-d485a2e342bc
-- title:
--   F256 Garcia Stichtenoth: exists eq algebra Map of step Auxiliary Polynomial aeval eq zero
-- statement:
--   Every root after scalar extension is the image of one of the sixteen
--   concrete residual roots.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ResidualPolynomial.lean#L50-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ResidualPolynomial.lean#L50-L59

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AuxiliaryMinpoly
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ResidualPolynomial
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.exists_eq_algebraMap_of_stepAuxiliaryPolynomial_aeval_eq_zero
    {E : Type*} [Field E] [Algebra F256 E] (a : F256) (y : E)
    (hy : Polynomial.aeval y (stepAuxiliaryPolynomial a) = 0) :
    ∃ b ∈ f256ArtinSchreierRoots a,
      y = algebraMap F256 E b := by sorry
