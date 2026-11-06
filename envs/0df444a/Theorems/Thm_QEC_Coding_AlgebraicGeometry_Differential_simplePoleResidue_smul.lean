-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_smul
-- name    : QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:32:54.521203+00:00
-- url     : https://prove2.me/theorems/e768cd47-a47e-4f72-8215-77a331bb53f0
-- title:
--   Differential: simple Pole Residue smul
-- statement:
--   The normalized simple-pole residue is linear over the valuation ring;
--   the induced scalar on the residue field is the actual reduction of the
--   regular function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/ResidueProduct.lean#L74-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/ResidueProduct.lean#L74-L80

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

theorem QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_smul (P : GlobalPlace k F)
    (f : P.valuationRing) (omega : simplePoleDifferentialLattice P) :
    simplePoleResidue (k := k) (F := F) P (f • omega) =
      P.residue f * simplePoleResidue (k := k) (F := F) P omega := by sorry
