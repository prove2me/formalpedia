-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathScheduleTypedSuccessfulOutputCost_eq
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathScheduleTypedSuccessfulOutputCost_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:42:32.926065+00:00
-- url     : https://prove2.me/theorems/480d7956-d251-404e-a75b-846f23fadb81
-- title:
--   BH12 Concatenation: bh12 Path Schedule Typed Successful Output Cost eq
-- statement:
--   The indexed typed cost is definitionally the actual finite-path cost.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2698-L2707
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2698-L2707

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathScheduleTypedSuccessfulOutputCost_eq (q : Nat)
    (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (index : BH12PathScheduleIndex q) :
    bh12PathScheduleTypedSuccessfulOutputCost q p hsmall hhalf hstrong index =
      bh12PathTypedSuccessfulOutputCost q p hsmall hhalf hstrong
        index.depth index.path := by sorry
