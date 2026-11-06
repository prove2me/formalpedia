-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidue_apply
-- name    : QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidue_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:35:18.951134+00:00
-- url     : https://prove2.me/theorems/0d23bc5b-762b-4637-aa4c-823441d87d19
-- title:
--   Differential: global Simple Pole Residue apply
-- statement:
--   A coefficient of the global residue `Finsupp` is the traced normalized
--   local residue at that place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/SimplePoleResidue.lean#L123-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/SimplePoleResidue.lean#L123-L128

import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_Residue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidue_apply
    (omega : Differential k F) (homega : IsGlobalSimplePole omega)
    (P : GlobalPlace k F) :
    globalSimplePoleResidue (k := k) (F := F) omega homega P =
      globalSimplePoleResidueCoefficient (k := k) (F := F) omega homega P := by sorry
