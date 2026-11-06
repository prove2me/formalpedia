-- Prove2me | Theorems.Thm_QEC_Semantics_positiveSupportProjection_mul_negativeSupportProjection
-- name    : QEC.Semantics.positiveSupportProjection_mul_negativeSupportProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:41:03.122382+00:00
-- url     : https://prove2.me/theorems/03e2d759-65ca-4ccc-9486-958495ac62a0
-- title:
--   Semantics: positive Support Projection mul negative Support Projection
-- statement:
--   The support projections of the positive and negative parts are orthogonal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L295-L297
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L295-L297

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

theorem QEC.Semantics.positiveSupportProjection_mul_negativeSupportProjection (A : Operator H) :
    positiveSupportProjection A * negativeSupportProjection A = 0 := by sorry
