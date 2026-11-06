-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_traceNorm_projectedTail_eq_complementTrace
-- name    : QEC.Semantics.DensityOperator.traceNorm_projectedTail_eq_complementTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:11:59.39219+00:00
-- url     : https://prove2.me/theorems/1b948845-1d6e-4657-8718-666680296af4
-- title:
--   Density Operator: trace Norm projected Tail eq complement Trace
-- statement:
--   The Density Operator construction uses the trace Norm projected Tail eq complement Trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L492-L496
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L492-L496

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

theorem QEC.Semantics.DensityOperator.traceNorm_projectedTail_eq_complementTrace [Nontrivial H]
    (P : Operator H) (hP : IsStarProjection P) (rho : DensityOperator H) :
    traceNorm (projectedTail P rho.toOperator) =
      Complex.re (LinearMap.trace Complex H ((1 - P) * rho.toOperator)) := by sorry
