-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathYieldFactor_eq_oneLevelFamilySuccess
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathYieldFactor_eq_oneLevelFamilySuccess
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:42:48.320715+00:00
-- url     : https://prove2.me/theorems/7d5850ba-0c9d-491d-805f-6a05f278f555
-- title:
--   BH12 Concatenation: bh12 Path Yield Factor eq one Level Family Success
-- statement:
--   The same factor is the success probability retained by the corresponding
--   one-level selected-port family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2285-L2297
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2285-L2297

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathYieldFactor_eq_oneLevelFamilySuccess (q : Nat)
    (p : ErrorParameter) (z : Nat) (path : depthOutputPath q z) (stage : Fin z)
    (hhalf : (bh12PathParameter q p stage.1
      (bh12PathStage q z path stage)).rate ≤ 1 / 2) :
    bh12PathYieldFactor q p z path stage =
      ((bh12OneLevelProtocolFamily q
        (bh12PathParameter q p stage.1 (bh12PathStage q z path stage)) hhalf).protocol
        (path stage)).run.successProbability := by sorry
