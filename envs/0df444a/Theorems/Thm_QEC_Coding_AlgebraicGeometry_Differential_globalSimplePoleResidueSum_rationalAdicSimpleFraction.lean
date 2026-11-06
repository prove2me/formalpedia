-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidueSum_rationalAdicSimpleFraction
-- name    : QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidueSum_rationalAdicSimpleFraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:41:59.957955+00:00
-- url     : https://prove2.me/theorems/e14f4752-b7a7-4d69-947e-b4e398a4bfb8
-- title:
--   Differential: global Simple Pole Residue Sum rational Adic Simple Fraction
-- statement:
--   The finite global traced-residue sum of a proper rational simple fraction
--   vanishes: its denominator-place residue cancels its infinity residue.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/SimpleFractionGlobalResidue.lean#L169-L270
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/SimpleFractionGlobalResidue.lean#L169-L270

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSimpleFractionResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinitySimpleFractionResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SimpleFractionGlobalResidue
set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidueSum_rationalAdicSimpleFraction
    (q : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X])
    (hb : b.degree < (GlobalPlace.rationalAdicPolynomial q).degree) :
    globalSimplePoleResidueSum (k := k) (F := RatFunc k)
        ((rationalAdicSimpleFractionAtSimplePole q b :
          simplePoleDifferentialLattice (GlobalPlace.rationalAdic q)) :
            Differential k (RatFunc k))
        (rationalAdicSimpleFraction_isGlobalSimplePole q b hb) = 0 := by sorry
