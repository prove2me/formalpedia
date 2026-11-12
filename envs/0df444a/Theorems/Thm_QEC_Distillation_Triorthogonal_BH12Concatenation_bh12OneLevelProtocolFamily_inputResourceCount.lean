-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12OneLevelProtocolFamily_inputResourceCount
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12OneLevelProtocolFamily_inputResourceCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:28:42.840351+00:00
-- url     : https://prove2.me/theorems/c1c709f6-6384-4bb9-9b28-78737a853ddd
-- title:
--   BH12 Concatenation: bh12 One Level Protocol Family input Resource Count
-- statement:
--   The #458 input count is the actual physical BH12 resource count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2099-L2103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2099-L2103

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12OneLevelProtocolFamily_inputResourceCount (q : Nat)
    (p : ErrorParameter) (hhalf : p.rate ≤ 1 / 2) (port : OddRow q) :
    (bh12OneLevelProtocolFamily q p hhalf).inputResourceCount port =
      bh12InputCount q := by sorry
