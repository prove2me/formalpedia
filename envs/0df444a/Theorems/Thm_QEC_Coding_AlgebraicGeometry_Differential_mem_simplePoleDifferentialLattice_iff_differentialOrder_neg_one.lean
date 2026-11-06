-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
-- name    : QEC.Coding.AlgebraicGeometry.Differential.mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:24:44.872782+00:00
-- url     : https://prove2.me/theorems/e7006e06-0606-476e-a6ff-fe30a038b8b7
-- title:
--   Differential: mem simple Pole Differential Lattice iff differential Order neg one
-- statement:
--   A nonzero differential has at most a simple pole at a place exactly when
--   its intrinsic local differential order is at least `-1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/LocalDifferentialOrder.lean#L84-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/LocalDifferentialOrder.lean#L84-L98

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalUniformizerDerivative
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalDifferentialOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.Differential.mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
    (P : GlobalPlace k F) (omega : Differential k F) (homega : omega ≠ 0) :
    omega ∈ simplePoleDifferentialLattice P ↔
      -1 ≤ differentialOrder (k := k) (F := F) P omega homega := by sorry
