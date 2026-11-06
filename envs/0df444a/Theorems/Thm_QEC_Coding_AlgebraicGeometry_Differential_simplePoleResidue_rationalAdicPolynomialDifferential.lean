-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_rationalAdicPolynomialDifferential
-- name    : QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_rationalAdicPolynomialDifferential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:33:25.259198+00:00
-- url     : https://prove2.me/theorems/decc2202-1c72-4194-852a-4c353432ec3b
-- title:
--   Differential: simple Pole Residue rational Adic Polynomial Differential
-- statement:
--   Polynomial differentials have zero normalized residue at every finite
--   rational place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicPolynomialDifferential.lean#L89-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicPolynomialDifferential.lean#L89-L97

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_Residue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialDifferential
set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_rationalAdicPolynomialDifferential
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (rationalAdicPolynomialDifferentialAtSimplePole p b) = 0 := by sorry
