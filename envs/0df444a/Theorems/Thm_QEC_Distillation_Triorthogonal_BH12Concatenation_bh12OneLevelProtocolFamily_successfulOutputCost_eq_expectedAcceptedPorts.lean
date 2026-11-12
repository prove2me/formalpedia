-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12OneLevelProtocolFamily_successfulOutputCost_eq_expectedAcceptedPorts
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12OneLevelProtocolFamily_successfulOutputCost_eq_expectedAcceptedPorts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:41:20.826571+00:00
-- url     : https://prove2.me/theorems/5b2ccae6-6dc0-4bda-9371-297e8368f074
-- title:
--   BH12 Concatenation: bh12 One Level Protocol Family successful Output Cost eq expected Accepted Ports
-- statement:
--   The same one-level cost is input resources divided by the literal flagged
--   batch expected accepted-port yield.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2153-L2159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2153-L2159

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12OneLevelProtocolFamily_successfulOutputCost_eq_expectedAcceptedPorts
    (q : Nat) (p : ErrorParameter) (hhalf : p.rate ≤ 1 / 2) (port : OddRow q) :
    (bh12OneLevelProtocolFamily q p hhalf).successfulOutputCost port =
      (bh12InputCount q : ℝ) /
        DependentBatch.expectedAcceptedPorts (bh12PhysicalFlaggedBatch q p) := by sorry
