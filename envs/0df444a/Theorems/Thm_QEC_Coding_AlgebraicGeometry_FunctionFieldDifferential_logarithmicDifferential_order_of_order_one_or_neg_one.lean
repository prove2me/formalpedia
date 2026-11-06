-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_logarithmicDifferential_order_of_order_one_or_neg_one
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.logarithmicDifferential_order_of_order_one_or_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:42:37.486673+00:00
-- url     : https://prove2.me/theorems/a71f4e06-ec43-426b-bc56-68b8edb65761
-- title:
--   Function Field Differential: logarithmic Differential order of order one or neg one
-- statement:
--   The Function Field Differential construction uses the logarithmic Differential order of order one or neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/ParameterDifferentialOrder.lean#L30-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/ParameterDifferentialOrder.lean#L30-L54

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ParameterDifferentialOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
noncomputable section
variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [Algebra.IsSeparable (RatFunc k) K] [FiniteDimensional (RatFunc k) K]

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.logarithmicDifferential_order_of_order_one_or_neg_one
    (P : GlobalPlace k K) (f : K) (hf : f ≠ 0)
    (horder : P.order f = 1 ∨ P.order f = -1) :
    differentialOrder P (Differential.logarithmicDifferential (k := k) f)
      (logarithmicDifferential_ne_zero_of_order_one_or_neg_one P f hf horder) = -1 := by sorry
