-- Prove2me | Theorems.Thm_QEC_Distillation_DistillationProtocolFamily_inputOutputRatio_nonneg
-- name    : QEC.Distillation.DistillationProtocolFamily.inputOutputRatio_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:18:43.399469+00:00
-- url     : https://prove2.me/theorems/29f31c37-5f9b-48c2-a0a8-ac13e9941d16
-- title:
--   Distillation Protocol Family: input Output Ratio nonneg
-- statement:
--   The direct input-output ratio is nonnegative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/Overhead.lean#L77-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/Overhead.lean#L77-L82

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

theorem QEC.Distillation.DistillationProtocolFamily.inputOutputRatio_nonneg
    (family : DistillationProtocolFamily Resource Input Output Index)
    (index : Index) :
    0 ≤ family.inputOutputRatio index := by sorry
