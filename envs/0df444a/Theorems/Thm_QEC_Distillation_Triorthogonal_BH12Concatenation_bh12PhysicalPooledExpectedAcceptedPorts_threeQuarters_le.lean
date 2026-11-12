-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PhysicalPooledExpectedAcceptedPorts_threeQuarters_le
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PhysicalPooledExpectedAcceptedPorts_threeQuarters_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:39:33.530474+00:00
-- url     : https://prove2.me/theorems/ef5d522f-de9d-462d-bc6d-f587b64fb0c4
-- title:
--   BH12 Concatenation: bh12 Physical Pooled Expected Accepted Ports three Quarters le
-- statement:
--   Small physical input error yields the pooled three-quarters lower bound
--   by finite linearity alone.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2018-L2030
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2018-L2030

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PhysicalPooledExpectedAcceptedPorts_threeQuarters_le
    (q : Nat) (p : ErrorParameter) (count : Nat)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4) :
    (count : ℝ) * (bh12OutputCount q : ℝ) * ((3 : ℝ) / 4) ≤
      DependentBatch.pooledExpectedAcceptedPorts count
        (bh12PhysicalFlaggedPool q p count) := by sorry
