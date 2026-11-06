-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_smul_eq_zero_of_mem_maximalIdeal
-- name    : QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_smul_eq_zero_of_mem_maximalIdeal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:33:23.611216+00:00
-- url     : https://prove2.me/theorems/c4cc4d3b-a4cf-4dd0-a446-0fcdcd94cc00
-- title:
--   Differential: simple Pole Residue smul eq zero of mem maximal Ideal
-- statement:
--   A regular scalar in the maximal ideal kills every normalized
--   simple-pole residue.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/ResidueProduct.lean#L84-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/ResidueProduct.lean#L84-L90

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

theorem QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_smul_eq_zero_of_mem_maximalIdeal
    (P : GlobalPlace k F) (f : P.valuationRing)
    (hf : f ∈ IsLocalRing.maximalIdeal P.valuationRing)
    (omega : simplePoleDifferentialLattice P) :
    simplePoleResidue (k := k) (F := F) P (f • omega) = 0 := by sorry
