-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12OneLevelProtocolFamily_successfulOutputError_le_targetError
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12OneLevelProtocolFamily_successfulOutputError_le_targetError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:40:52.857805+00:00
-- url     : https://prove2.me/theorems/d507660c-e059-4941-b1c3-1320d403ddfe
-- title:
--   BH12 Concatenation: bh12 One Level Protocol Family successful Output Error le target Error
-- statement:
--   The selected protocol's successful output error obeys its exact family
--   target through #755's physical quadratic theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2131-L2137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2131-L2137

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12OneLevelProtocolFamily_successfulOutputError_le_targetError
    (q : Nat) (p : ErrorParameter) (hhalf : p.rate ≤ 1 / 2) (port : OddRow q) :
    ((bh12OneLevelProtocolFamily q p hhalf).protocol port).successfulOutputError ≤
      quadraticCoefficient q * p.rate ^ 2 := by sorry
