-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
-- name    : QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:33:16.234001+00:00
-- url     : https://prove2.me/theorems/c7dbe814-3f15-4be2-8bf2-86d7229dbe44
-- title:
--   Differential: coe rational Adic Polynomial Differential
-- statement:
--   The regular local polynomial differential has the expected ambient
--   coefficient and differential generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicPolynomialDifferential.lean#L64-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicPolynomialDifferential.lean#L64-L75

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_Residue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialDifferential
set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    ((rationalAdicPolynomialDifferential p b :
      localDifferentialLattice (GlobalPlace.rationalAdic p)) :
        Differential k (RatFunc k)) =
      algebraMap k[X] (RatFunc k) b •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by sorry
