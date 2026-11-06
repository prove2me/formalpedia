-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidueEquiv_unique
-- name    : QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidueEquiv_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:32:38.256066+00:00
-- url     : https://prove2.me/theorems/d2d9bdc1-1ae1-4beb-8ec6-369cc3eb1b26
-- title:
--   Differential: simple Pole Residue Equiv unique
-- statement:
--   The normalization on the logarithmic uniformizer class uniquely
--   characterizes the simple-pole residue equivalence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/Residue.lean#L75-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/Residue.lean#L75-L99

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

theorem QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidueEquiv_unique
    (P : GlobalPlace k F)
    (e : localResidueLine P ≃ₗ[P.valuationRing] GlobalPlace.residueField P)
    (he : e (uniformizerLogDifferentialClass (k := k) (F := F) P) = 1) :
    e = simplePoleResidueEquiv (k := k) (F := F) P := by sorry
