-- Prove2me | Theorems.Thm_QEC_Distillation_DistillationProtocolFamily_inputOutputRatio_le_successfulOutputCost
-- name    : QEC.Distillation.DistillationProtocolFamily.inputOutputRatio_le_successfulOutputCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:59:34.373953+00:00
-- url     : https://prove2.me/theorems/bc6fa02c-512b-4a78-8507-0f8c51dbf3a8
-- title:
--   Distillation Protocol Family: input Output Ratio le successful Output Cost
-- statement:
--   Positive success makes direct input-output ratio no larger than successful-output cost.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/Overhead.lean#L114-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/Overhead.lean#L114-L122

import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_Overhead
set_option autoImplicit false
universe u
open QEC QEC.Distillation
open Semantics
open QEC.Distillation.DistillationProtocolFamily
variable {Resource Input Output Index : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]
variable [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
variable [FiniteQuantumSystem Input]
variable [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
variable [FiniteQuantumSystem Output]

theorem QEC.Distillation.DistillationProtocolFamily.inputOutputRatio_le_successfulOutputCost
    (family : DistillationProtocolFamily Resource Input Output Index)
    (index : Index)
    (hsuccess : 0 < (family.protocol index).run.successProbability) :
    family.inputOutputRatio index ≤ family.successfulOutputCost index := by sorry
