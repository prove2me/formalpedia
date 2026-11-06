-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidueSum_add
-- name    : QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidueSum_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:39:13.656562+00:00
-- url     : https://prove2.me/theorems/010f578c-8aff-4054-9e3e-a82d55da5b7b
-- title:
--   Differential: global Simple Pole Residue Sum add
-- statement:
--   The finite global residue sum is additive.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/SimplePoleResidueLinear.lean#L102-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/SimplePoleResidueLinear.lean#L102-L110

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

theorem QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidueSum_add (omega eta : Differential k F)
    (homega : IsGlobalSimplePole (k := k) (F := F) omega)
    (heta : IsGlobalSimplePole (k := k) (F := F) eta) :
    globalSimplePoleResidueSum (k := k) (F := F) (omega + eta)
        (homega.add heta) =
      globalSimplePoleResidueSum (k := k) (F := F) omega homega +
        globalSimplePoleResidueSum (k := k) (F := F) eta heta := by sorry
