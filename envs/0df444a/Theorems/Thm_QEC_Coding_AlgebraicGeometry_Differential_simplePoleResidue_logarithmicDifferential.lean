-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_logarithmicDifferential
-- name    : QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_logarithmicDifferential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:36:07.338186+00:00
-- url     : https://prove2.me/theorems/a8a8a849-e9c3-4f9a-9cf0-9d3a97b117ad
-- title:
--   Differential: simple Pole Residue logarithmic Differential
-- statement:
--   The normalized local residue of `df / f` is the integer order of `f`,
--   reduced in the actual residue field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/LogarithmicResidue.lean#L157-L181
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/LogarithmicResidue.lean#L157-L181

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
open QEC.Coding.AlgebraicGeometry.Differential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_logarithmicDifferential
    (P : GlobalPlace k F) (f : F) (hf : f ≠ 0) :
    simplePoleResidue (k := k) (F := F) P
        (logarithmicDifferentialAtSimplePole (k := k) (F := F) P f hf) =
      (P.order f : GlobalPlace.residueField P) := by sorry
