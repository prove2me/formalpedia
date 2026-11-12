-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PhysicalPooledExpectedAcceptedPorts
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PhysicalPooledExpectedAcceptedPorts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:28:43.35121+00:00
-- url     : https://prove2.me/theorems/1b1ca63d-38b1-4948-95f2-e88f53a6a22d
-- title:
--   BH12 Concatenation: bh12 Physical Pooled Expected Accepted Ports
-- statement:
--   Finite linearity gives the pooled expected accepted-port count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2007-L2014
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2007-L2014

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PhysicalPooledExpectedAcceptedPorts (q : Nat) (p : ErrorParameter)
    (count : Nat) :
    DependentBatch.pooledExpectedAcceptedPorts count
        (bh12PhysicalFlaggedPool q p count) =
      (count : ℝ) * (bh12OutputCount q : ℝ) * rawSuccessMass q p := by sorry
