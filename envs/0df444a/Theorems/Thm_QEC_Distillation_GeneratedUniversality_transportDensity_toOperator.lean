-- Prove2me | Theorems.Thm_QEC_Distillation_GeneratedUniversality_transportDensity_toOperator
-- name    : QEC.Distillation.GeneratedUniversality.transportDensity_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:10:08.784266+00:00
-- url     : https://prove2.me/theorems/9f0830db-557c-41b4-8866-254635a1a404
-- title:
--   Generated Universality: transport Density to Operator
-- statement:
--   The generated-universality density action is the semantic unitary conjugation action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L326-L330
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L326-L330

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
set_option autoImplicit false
noncomputable section
universe u
open QEC
open QEC.Distillation
open QEC.Distillation.GeneratedUniversality
open Semantics
open scoped Matrix.Norms.Elementwise

theorem QEC.Distillation.GeneratedUniversality.transportDensity_toOperator {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (U : UnitaryTransport H H) (rho : DensityOperator H) :
    (transportDensity U rho).toOperator = U.conjOperator rho.toOperator := by sorry
