-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleTraceResidue_zero
-- name    : QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:36:32.499536+00:00
-- url     : https://prove2.me/theorems/55456a44-5d2c-4d1a-8264-8dab84e820af
-- title:
--   Differential: simple Pole Trace Residue zero
-- statement:
--   The traced residue of the zero differential is zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/SimplePoleResidueLinear.lean#L48-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/SimplePoleResidueLinear.lean#L48-L53

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidueLinear
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue_zero (P : GlobalPlace k F) :
    simplePoleTraceResidue (k := k) (F := F) P 0
      (simplePoleDifferentialLattice P).zero_mem = 0 := by sorry
