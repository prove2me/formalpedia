-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
-- name    : QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:32:11.281969+00:00
-- url     : https://prove2.me/theorems/eb7c0bd1-32ca-46e8-b0fa-579dd0bf4da4
-- title:
--   Differential: simple Pole Residue eq zero of mem local Differential Lattice
-- statement:
--   Regular differentials have zero simple-pole residue.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/Residue.lean#L117-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/Residue.lean#L117-L126

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalUniformizerDerivative
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_Residue
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
    (P : GlobalPlace k F) (omega : simplePoleDifferentialLattice P)
    (homega : (omega : Differential k F) ∈ localDifferentialLattice P) :
    simplePoleResidue (k := k) (F := F) P omega = 0 := by sorry
