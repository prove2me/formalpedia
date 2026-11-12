-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathSchedule_yield_pos
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathSchedule_yield_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:28:47.616191+00:00
-- url     : https://prove2.me/theorems/00617bd0-3ad8-4c59-92cf-4651bcfe4768
-- title:
--   BH12 Concatenation: bh12 Path Schedule yield pos
-- statement:
--   The actual accounting yield is strictly positive at every indexed finite
--   path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2726-L2734
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2726-L2734

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathSchedule_yield_pos (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (index : BH12PathScheduleIndex q) :
    0 < (bh12PathScheduleTypedYieldFactor q p hsmall hhalf hstrong index : ℝ) := by sorry
