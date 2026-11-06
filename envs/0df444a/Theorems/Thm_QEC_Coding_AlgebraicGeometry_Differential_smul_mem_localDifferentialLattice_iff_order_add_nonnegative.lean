-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_smul_mem_localDifferentialLattice_iff_order_add_nonnegative
-- name    : QEC.Coding.AlgebraicGeometry.Differential.smul_mem_localDifferentialLattice_iff_order_add_nonnegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:33:11.605205+00:00
-- url     : https://prove2.me/theorems/a620bf7e-72e2-45bf-b7e7-851f4da09d6d
-- title:
--   Differential: smul mem local Differential Lattice iff order add nonnegative
-- statement:
--   A function-scaled nonzero differential is regular exactly when the sum
--   of the function order and differential order is nonnegative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/ResidueProduct.lean#L51-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/ResidueProduct.lean#L51-L58

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_Residue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.Differential.smul_mem_localDifferentialLattice_iff_order_add_nonnegative
    (P : GlobalPlace k F) (f : F) (hf : f ≠ 0)
    (omega : Differential k F) (homega : omega ≠ 0) :
    f • omega ∈ localDifferentialLattice P ↔
      0 ≤ P.order f + differentialOrder (k := k) (F := F) P omega homega := by sorry
