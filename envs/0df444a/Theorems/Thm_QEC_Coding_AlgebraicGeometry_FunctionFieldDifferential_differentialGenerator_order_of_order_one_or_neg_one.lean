-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialGenerator_order_of_order_one_or_neg_one
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialGenerator_order_of_order_one_or_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:41:13.287293+00:00
-- url     : https://prove2.me/theorems/7c30af5f-9e14-4879-80a3-db6ae7153555
-- title:
--   Function Field Differential: differential Generator order of order one or neg one
-- statement:
--   At a simple zero or pole, the order of the actual global differential
--   generator is determined by the derivative of that local parameter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/ParameterDifferentialOrder.lean#L58-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/ParameterDifferentialOrder.lean#L58-L90

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ParameterDifferentialOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
noncomputable section
variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [Algebra.IsSeparable (RatFunc k) K] [FiniteDimensional (RatFunc k) K]

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialGenerator_order_of_order_one_or_neg_one
    (P : GlobalPlace k K) (f : K) (hf : f ≠ 0)
    (horder : P.order f = 1 ∨ P.order f = -1) :
    ∃ _hdf : functionFieldDerivation (k := k) f ≠ 0,
      differentialOrder P (functionFieldDifferentialGenerator (k := k) (F := K))
        functionFieldDifferentialGenerator_ne_zero =
          P.order f - 1 - P.order (functionFieldDerivation (k := k) f) := by sorry
