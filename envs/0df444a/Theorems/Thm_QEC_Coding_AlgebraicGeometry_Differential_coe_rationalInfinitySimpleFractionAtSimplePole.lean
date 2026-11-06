-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalInfinitySimpleFractionAtSimplePole
-- name    : QEC.Coding.AlgebraicGeometry.Differential.coe_rationalInfinitySimpleFractionAtSimplePole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:37:32.9357+00:00
-- url     : https://prove2.me/theorems/544a0271-6dfb-462f-ac40-cf1394bc1d47
-- title:
--   Differential: coe rational Infinity Simple Fraction At Simple Pole
-- statement:
--   The infinity local representative has underlying differential
--   `(b / q) dX`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/InfinitySimpleFractionResidue.lean#L162-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/InfinitySimpleFractionResidue.lean#L162-L183

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinityResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinitySimpleFractionResidue
set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.Differential.coe_rationalInfinitySimpleFractionAtSimplePole
    (q b : k[X]) (hq : q.Monic) (hb : b.degree < q.degree) :
    ((rationalInfinitySimpleFractionAtSimplePole q b hq hb :
      simplePoleDifferentialLattice (GlobalPlace.rationalInfinity k)) :
        Differential k (RatFunc k)) =
        (algebraMap k[X] (RatFunc k) b /
        algebraMap k[X] (RatFunc k) q) •
          functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by sorry
