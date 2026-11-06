-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_rationalAdicWeightedPolynomialLogDifferential
-- name    : QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_rationalAdicWeightedPolynomialLogDifferential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:37:37.774295+00:00
-- url     : https://prove2.me/theorems/9bcf3f07-d67d-4fcb-959a-dc02085aaec6
-- title:
--   Differential: simple Pole Residue rational Adic Weighted Polynomial Log Differential
-- statement:
--   The normalized residue of the weighted logarithmic differential is the
--   reduced coefficient times the exact principal-ideal multiplicity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicPolynomialLogarithmicResidue.lean#L112-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/AdicPolynomialLogarithmicResidue.lean#L112-L126

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

theorem QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_rationalAdicWeightedPolynomialLogDifferential
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (r a : k[X]) (ha : a ≠ 0) :
    simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (rationalAdicWeightedPolynomialLogDifferentialAtSimplePole p r a ha) =
      (GlobalPlace.rationalAdic p).residue
          (GlobalPlace.rationalAdicPolynomialToValuationRing p r) *
        (multiplicity p.asIdeal (Ideal.span ({a} : Set k[X])) :
          (GlobalPlace.rationalAdic p).residueField) := by sorry
