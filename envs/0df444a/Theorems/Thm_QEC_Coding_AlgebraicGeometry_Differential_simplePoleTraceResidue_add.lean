-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleTraceResidue_add
-- name    : QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:36:35.113962+00:00
-- url     : https://prove2.me/theorems/f155e622-60e6-49b4-b56a-5320f84ad457
-- title:
--   Differential: simple Pole Trace Residue add
-- statement:
--   The constant-field trace of the normalized simple-pole residue is
--   additive.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/SimplePoleResidueLinear.lean#L57-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/SimplePoleResidueLinear.lean#L57-L70

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidueLinear
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue_add (P : GlobalPlace k F)
    (omega eta : Differential k F)
    (homega : omega ∈ simplePoleDifferentialLattice P)
    (heta : eta ∈ simplePoleDifferentialLattice P) :
    simplePoleTraceResidue (k := k) (F := F) P (omega + eta)
        ((simplePoleDifferentialLattice P).add_mem homega heta) =
      simplePoleTraceResidue (k := k) (F := F) P omega homega +
        simplePoleTraceResidue (k := k) (F := F) P eta heta := by sorry
