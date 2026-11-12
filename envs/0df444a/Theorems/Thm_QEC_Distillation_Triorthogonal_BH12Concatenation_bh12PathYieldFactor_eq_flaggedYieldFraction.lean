-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathYieldFactor_eq_flaggedYieldFraction
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathYieldFactor_eq_flaggedYieldFraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:42:55.527674+00:00
-- url     : https://prove2.me/theorems/f3cce4d4-187a-4f34-a20f-d69f55a28a76
-- title:
--   BH12 Concatenation: bh12 Path Yield Factor eq flagged Yield Fraction
-- statement:
--   The actual one-level flagged-batch expected yield, normalized by its
--   literal number of output ports, is the same path accounting factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2301-L2319
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2301-L2319

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathYieldFactor_eq_flaggedYieldFraction (q : Nat)
    (p : ErrorParameter) (z : Nat) (path : depthOutputPath q z) (stage : Fin z) :
    bh12PathYieldFactor q p z path stage =
      DependentBatch.expectedAcceptedPorts (bh12PhysicalFlaggedBatch q
        (bh12PathParameter q p stage.1 (bh12PathStage q z path stage))) /
        (bh12OutputCount q : ℝ) := by sorry
