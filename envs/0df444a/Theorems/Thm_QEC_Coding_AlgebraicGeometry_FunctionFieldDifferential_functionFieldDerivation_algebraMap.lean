-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDerivation_algebraMap
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDerivation_algebraMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:41:14.896182+00:00
-- url     : https://prove2.me/theorems/7b83c94f-c4ac-4ca2-b14e-6636aafe3daa
-- title:
--   Function Field Differential: function Field Derivation algebra Map
-- statement:
--   Uniqueness of separable derivation extension makes the ordinary
--   function-field derivations commute with any compatible field inclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/ParameterDifferentialOrder.lean#L100-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/ParameterDifferentialOrder.lean#L100-L114

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ParameterDifferentialOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
noncomputable section
variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [Algebra.IsSeparable (RatFunc k) K] [FiniteDimensional (RatFunc k) K]
variable {L : Type*} [Field L] [Algebra k L] [Algebra (RatFunc k) L]
    [IsScalarTower k (RatFunc k) L]
    [Algebra.IsSeparable (RatFunc k) L] [FiniteDimensional (RatFunc k) L]
    [Algebra K L] [IsScalarTower k K L] [IsScalarTower (RatFunc k) K L]
omit [Finite k]

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDerivation_algebraMap (x : K) :
    functionFieldDerivation (k := k) (F := L) (algebraMap K L x) =
      algebraMap K L (functionFieldDerivation (k := k) (F := K) x) := by sorry
