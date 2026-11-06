-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleTraceResidue_rationalInfinitySimpleFraction
-- name    : QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue_rationalInfinitySimpleFraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:39:35.559921+00:00
-- url     : https://prove2.me/theorems/00a10430-3b2a-42f5-ae7a-3c165d8947cd
-- title:
--   Differential: simple Pole Trace Residue rational Infinity Simple Fraction
-- statement:
--   The traced normalized residue at infinity of `(b / q) dX` is the
--   negative next-to-leading coefficient of `b`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/InfinitySimpleFractionResidue.lean#L267-L288
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/InfinitySimpleFractionResidue.lean#L267-L288

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

theorem QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue_rationalInfinitySimpleFraction
    (q b : k[X]) (hq : q.Monic) (hb : b.degree < q.degree) :
    simplePoleTraceResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalInfinity k)
        (rationalInfinitySimpleFractionAtSimplePole q b hq hb :
          Differential k (RatFunc k))
        (rationalInfinitySimpleFractionAtSimplePole q b hq hb).property =
      -b.coeff (q.natDegree - 1) := by sorry
