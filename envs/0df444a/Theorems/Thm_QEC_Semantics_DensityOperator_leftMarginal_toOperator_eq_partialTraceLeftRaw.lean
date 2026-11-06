-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_leftMarginal_toOperator_eq_partialTraceLeftRaw
-- name    : QEC.Semantics.DensityOperator.leftMarginal_toOperator_eq_partialTraceLeftRaw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:19:02.023076+00:00
-- url     : https://prove2.me/theorems/2c357c6e-8d6d-4dae-bfc8-e31b4c255372
-- title:
--   Density Operator: left Marginal to Operator eq partial Trace Left Raw
-- statement:
--   The left marginal is the raw left partial trace packaged as a density operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L553-L558
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Subadditivity.lean#L553-L558

import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder Kronecker TensorProduct
noncomputable section
open QEC.Semantics.DensityOperator

theorem QEC.Semantics.DensityOperator.leftMarginal_toOperator_eq_partialTraceLeftRaw
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] (rho : DensityOperator (CompositeSystem H K)) :
    (leftMarginal rho).toOperator = FiniteMatrixEntropy.partialTraceLeftRaw H K rho.toOperator := by sorry
