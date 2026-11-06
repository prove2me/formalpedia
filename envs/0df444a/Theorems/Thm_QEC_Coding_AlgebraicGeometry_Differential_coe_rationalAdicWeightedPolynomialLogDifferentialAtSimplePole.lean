-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicWeightedPolynomialLogDifferentialAtSimplePole
-- name    : QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicWeightedPolynomialLogDifferentialAtSimplePole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:37:22.952815+00:00
-- url     : https://prove2.me/theorems/c70235d6-02d6-4547-b4ba-f40f74d37c71
-- title:
--   Differential: coe rational Adic Weighted Polynomial Log Differential At Simple Pole
-- statement:
--   The weighted local logarithmic differential has its expected ambient
--   rational-function coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicPolynomialLogarithmicResidue.lean#L88-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicPolynomialLogarithmicResidue.lean#L88-L108

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialLogarithmicResidue
set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicWeightedPolynomialLogDifferentialAtSimplePole
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (r a : k[X]) (ha : a ≠ 0) :
    ((rationalAdicWeightedPolynomialLogDifferentialAtSimplePole p r a ha :
      simplePoleDifferentialLattice (GlobalPlace.rationalAdic p)) :
        Differential k (RatFunc k)) =
      (algebraMap k[X] (RatFunc k) r *
          (algebraMap k[X] (RatFunc k) a)⁻¹ *
          algebraMap k[X] (RatFunc k) a.derivative) •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by sorry
