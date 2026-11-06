-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_mem_localDifferentialLattice_iff_differentialOrder_nonnegative
-- name    : QEC.Coding.AlgebraicGeometry.Differential.mem_localDifferentialLattice_iff_differentialOrder_nonnegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:24:23.550499+00:00
-- url     : https://prove2.me/theorems/76069cdb-0dea-4f43-84e6-53289dcfc4af
-- title:
--   Differential: mem local Differential Lattice iff differential Order nonnegative
-- statement:
--   A nonzero differential is regular at a place exactly when its intrinsic
--   local differential order is nonnegative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/LocalDifferentialOrder.lean#L34-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/LocalDifferentialOrder.lean#L34-L51

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

theorem QEC.Coding.AlgebraicGeometry.Differential.mem_localDifferentialLattice_iff_differentialOrder_nonnegative
    (P : GlobalPlace k F) (omega : Differential k F) (homega : omega ≠ 0) :
    omega ∈ localDifferentialLattice P ↔
      0 ≤ differentialOrder (k := k) (F := F) P omega homega := by sorry
