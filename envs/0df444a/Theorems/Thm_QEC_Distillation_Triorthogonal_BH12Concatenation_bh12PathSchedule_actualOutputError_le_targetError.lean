-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathSchedule_actualOutputError_le_targetError
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathSchedule_actualOutputError_le_targetError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:29:15.676535+00:00
-- url     : https://prove2.me/theorems/33f4ccda-8dd2-4dc3-b804-d64552ad3afe
-- title:
--   BH12 Concatenation: bh12 Path Schedule actual Output Error le target Error
-- statement:
--   The actual recursively reached output error is bounded by the indexed
--   compiled quadratic-envelope target.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2738-L2747
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2738-L2747

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathSchedule_actualOutputError_le_targetError (q : Nat)
    (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (index : BH12PathScheduleIndex q) :
    (bh12PathParameter q p index.depth index.path).rate ≤
      bh12PathScheduleTargetError q p index := by sorry
