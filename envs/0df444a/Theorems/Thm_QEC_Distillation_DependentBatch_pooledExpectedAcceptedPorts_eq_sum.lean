-- Prove2me | Theorems.Thm_QEC_Distillation_DependentBatch_pooledExpectedAcceptedPorts_eq_sum
-- name    : QEC.Distillation.DependentBatch.pooledExpectedAcceptedPorts_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:01:09.252981+00:00
-- url     : https://prove2.me/theorems/338c6172-c44d-4469-8833-58cfcd2b8d90
-- title:
--   Dependent Batch: pooled Expected Accepted Ports eq sum
-- statement:
--   Pool accounting is exactly the finite sum of the individual grid yields.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/DependentBatch.lean#L88-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/DependentBatch.lean#L88-L93

import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Core_DependentBatch
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.DependentBatch
open Semantics
open scoped BigOperators
universe u v

theorem QEC.Distillation.DependentBatch.pooledExpectedAcceptedPorts_eq_sum {Port : Type u} {Outcome : Type v}
    [Fintype Port] [Fintype Outcome] (count : Nat)
    (pool : Fin count → FiniteFlaggedBatch Port Outcome) :
    pooledExpectedAcceptedPorts count pool =
      ∑ grid, expectedAcceptedPorts (pool grid) := by sorry
