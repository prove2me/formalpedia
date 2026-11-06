-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_projectionTrace_add_complementTrace
-- name    : QEC.Semantics.DensityOperator.projectionTrace_add_complementTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:42:10.893597+00:00
-- url     : https://prove2.me/theorems/292e99b3-6322-4e66-a1d1-03b02ec3be9d
-- title:
--   Density Operator: projection Trace add complement Trace
-- statement:
--   The Density Operator construction uses the projection Trace add complement Trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L498-L501
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L498-L501

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
open QEC.Semantics.DensityOperator

theorem QEC.Semantics.DensityOperator.projectionTrace_add_complementTrace (P : Operator H) (rho : DensityOperator H) :
    LinearMap.trace Complex H (P * rho.toOperator) +
      LinearMap.trace Complex H ((1 - P) * rho.toOperator) = 1 := by sorry
