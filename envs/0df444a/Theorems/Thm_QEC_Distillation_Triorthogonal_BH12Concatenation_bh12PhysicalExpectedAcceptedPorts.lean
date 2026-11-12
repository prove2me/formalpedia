-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PhysicalExpectedAcceptedPorts
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PhysicalExpectedAcceptedPorts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:26:11.618801+00:00
-- url     : https://prove2.me/theorems/c771bc1b-babc-4306-8279-1deeac985bec
-- title:
--   BH12 Concatenation: bh12 Physical Expected Accepted Ports
-- statement:
--   The literal one-block accepted-port expectation is the actual output
--   count times the actual BH12 raw success mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1987-L1997
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1987-L1997

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PhysicalExpectedAcceptedPorts (q : Nat) (p : ErrorParameter) :
    DependentBatch.expectedAcceptedPorts (bh12PhysicalFlaggedBatch q p) =
      (bh12OutputCount q : ℝ) * rawSuccessMass q p := by sorry
