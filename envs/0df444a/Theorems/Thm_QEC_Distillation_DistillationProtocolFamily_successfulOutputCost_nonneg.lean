-- Prove2me | Theorems.Thm_QEC_Distillation_DistillationProtocolFamily_successfulOutputCost_nonneg
-- name    : QEC.Distillation.DistillationProtocolFamily.successfulOutputCost_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:59:23.745902+00:00
-- url     : https://prove2.me/theorems/5d1c4f7c-247f-4e0f-a4c1-3053d630f997
-- title:
--   Distillation Protocol Family: successful Output Cost nonneg
-- statement:
--   The successful-output cost is nonnegative, including at zero success.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/Overhead.lean#L85-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/Overhead.lean#L85-L92

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

theorem QEC.Distillation.DistillationProtocolFamily.successfulOutputCost_nonneg
    (family : DistillationProtocolFamily Resource Input Output Index)
    (index : Index) :
    0 ≤ family.successfulOutputCost index := by sorry
