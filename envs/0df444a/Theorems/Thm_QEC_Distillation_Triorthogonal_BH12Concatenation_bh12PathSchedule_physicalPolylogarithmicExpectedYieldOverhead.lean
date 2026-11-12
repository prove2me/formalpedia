-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathSchedule_physicalPolylogarithmicExpectedYieldOverhead
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathSchedule_physicalPolylogarithmicExpectedYieldOverhead
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:29:26.779895+00:00
-- url     : https://prove2.me/theorems/3b4e8a0d-4f14-4896-9a3b-e6b5a01a7dee
-- title:
--   BH12 Concatenation: bh12 Path Schedule physical Polylogarithmic Expected Yield Overhead
-- statement:
--   The BH12 path schedule realizes the additive, level-indexed
--   expected-yield overhead interface.  Its yield is the finite product of actual
--   one-level flagged expected-yield factors; it is not a joint binary success
--   probability for the whole varying-register construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2794-L2812
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2794-L2812

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathSchedule_physicalPolylogarithmicExpectedYieldOverhead
    (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (hp : 0 < p.rate) (hq : 0 < q) :
    DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
      (bh12PathScheduleInputSlots q) (bh12PathScheduleOutputSlots q)
      (bh12PathScheduleTargetError q p)
      (fun index => (bh12PathParameter q p index.depth index.path).rate)
      (bh12PathScheduleTypedYieldFactor q p hsmall hhalf hstrong)
      (bh12BlockExponent q) (bh12QuadraticEnvelopeCostCoefficient q p) := by sorry
