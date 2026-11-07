-- Prove2me | Theorems.Thm_QEC_Distillation_DistillationProtocolFamily_targetError_nonneg
-- name    : QEC.Distillation.DistillationProtocolFamily.targetError_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:59:16.093968+00:00
-- url     : https://prove2.me/theorems/7ae33426-ee0d-42b8-8f5e-ea74e004bb5c
-- title:
--   Distillation Protocol Family: target Error nonneg
-- statement:
--   Every target error is nonnegative because it bounds a nonnegative error.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/Overhead.lean#L46-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/Overhead.lean#L46-L54

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

theorem QEC.Distillation.DistillationProtocolFamily.targetError_nonneg
    (family : DistillationProtocolFamily Resource Input Output Index)
    (index : Index) :
    0 ≤ family.targetError index := by sorry
