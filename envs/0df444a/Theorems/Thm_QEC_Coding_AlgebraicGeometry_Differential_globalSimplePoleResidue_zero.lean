-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidue_zero
-- name    : QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidue_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:36:32.275114+00:00
-- url     : https://prove2.me/theorems/c76bb8bd-9b44-4d5a-84f2-00794f1820de
-- title:
--   Differential: global Simple Pole Residue zero
-- statement:
--   The finitely supported global residue family of zero is zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/SimplePoleResidueLinear.lean#L73-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/SimplePoleResidueLinear.lean#L73-L78

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidueLinear
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidue_zero :
    globalSimplePoleResidue (k := k) (F := F) 0
      (isGlobalSimplePole_zero (k := k) (F := F)) = 0 := by sorry
