-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidue_add
-- name    : QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidue_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:39:02.497393+00:00
-- url     : https://prove2.me/theorems/11cd4f3b-7aa3-49b8-ae6c-127b20dea367
-- title:
--   Differential: global Simple Pole Residue add
-- statement:
--   The finitely supported global residue family is additive.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/SimplePoleResidueLinear.lean#L81-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/SimplePoleResidueLinear.lean#L81-L92

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidueLinear
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_Nonnegative_add

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidue_add (omega eta : Differential k F)
    (homega : IsGlobalSimplePole (k := k) (F := F) omega)
    (heta : IsGlobalSimplePole (k := k) (F := F) eta) :
    globalSimplePoleResidue (k := k) (F := F) (omega + eta)
        (homega.add heta) =
      globalSimplePoleResidue (k := k) (F := F) omega homega +
        globalSimplePoleResidue (k := k) (F := F) eta heta := by sorry
