-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicSimpleFractionAtSimplePole
-- name    : QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicSimpleFractionAtSimplePole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:37:32.930294+00:00
-- url     : https://prove2.me/theorems/2d847275-f3aa-4e04-9af5-453905073db0
-- title:
--   Differential: coe rational Adic Simple Fraction At Simple Pole
-- statement:
--   The constructed local representative is the rational simple-fraction
--   differential `(b / q) dX`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicSimpleFractionResidue.lean#L142-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicSimpleFractionResidue.lean#L142-L158

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_EulerTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSimpleFractionResidue
set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicSimpleFractionAtSimplePole
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    ((rationalAdicSimpleFractionAtSimplePole p b :
      simplePoleDifferentialLattice (GlobalPlace.rationalAdic p)) :
        Differential k (RatFunc k)) =
      (algebraMap k[X] (RatFunc k) b /
        algebraMap k[X] (RatFunc k) (GlobalPlace.rationalAdicPolynomial p)) •
          functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by sorry
