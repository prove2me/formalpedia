-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_roots
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_roots
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:53:39.429496+00:00
-- url     : https://prove2.me/theorems/bdd2c09b-7204-4058-98b1-cef558f63902
-- title:
--   F256 Garcia Stichtenoth: step Auxiliary Polynomial roots
-- statement:
--   The roots of the residual auxiliary polynomial are exactly the concrete
--   sixteen-element Artin--Schreier fibre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ResidualPolynomial.lean#L20-L30
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ResidualPolynomial.lean#L20-L30

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AuxiliaryMinpoly
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ResidualPolynomial
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_roots (a : F256) :
    (stepAuxiliaryPolynomial a).roots =
      (f256ArtinSchreierRoots a : Finset F256).val := by sorry
