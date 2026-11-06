-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidueSum_zero
-- name    : QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidueSum_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:36:29.353138+00:00
-- url     : https://prove2.me/theorems/85ebfa96-7c81-451e-ba5a-06822126a18d
-- title:
--   Differential: global Simple Pole Residue Sum zero
-- statement:
--   The finite global residue sum of zero is zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/SimplePoleResidueLinear.lean#L95-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/SimplePoleResidueLinear.lean#L95-L99

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidueLinear
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidueSum_zero :
    globalSimplePoleResidueSum (k := k) (F := F) 0
      (isGlobalSimplePole_zero (k := k) (F := F)) = 0 := by sorry
