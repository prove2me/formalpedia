-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
-- name    : QEC.Coding.AlgebraicGeometry.Differential.smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:33:09.19995+00:00
-- url     : https://prove2.me/theorems/e73322e1-283e-499a-9fe8-3c205a0baae9
-- title:
--   Differential: smul mem simple Pole Differential Lattice iff order add neg one
-- statement:
--   A function-scaled nonzero differential has at most a simple pole exactly
--   when its summed local order is at least `-1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/ResidueProduct.lean#L62-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/ResidueProduct.lean#L62-L69

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

theorem QEC.Coding.AlgebraicGeometry.Differential.smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
    (P : GlobalPlace k F) (f : F) (hf : f ≠ 0)
    (omega : Differential k F) (homega : omega ≠ 0) :
    f • omega ∈ simplePoleDifferentialLattice P ↔
      -1 ≤ P.order f + differentialOrder (k := k) (F := F) P omega homega := by sorry
