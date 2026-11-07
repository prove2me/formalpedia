-- Prove2me | Theorems.Thm_QEC_Distillation_DistillationProtocolFamily_successfulOutputCost_denominator_pos
-- name    : QEC.Distillation.DistillationProtocolFamily.successfulOutputCost_denominator_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:59:31.239818+00:00
-- url     : https://prove2.me/theorems/6c05a2d6-77fd-4e08-a6f8-d2e23dc869d1
-- title:
--   Distillation Protocol Family: successful Output Cost denominator pos
-- statement:
--   Positive success makes the successful-output-cost denominator positive.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/Overhead.lean#L104-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/Overhead.lean#L104-L111

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

theorem QEC.Distillation.DistillationProtocolFamily.successfulOutputCost_denominator_pos
    (family : DistillationProtocolFamily Resource Input Output Index)
    (index : Index)
    (hsuccess : 0 < (family.protocol index).run.successProbability) :
    0 < (family.outputResourceCount index : ℝ) *
      (family.protocol index).run.successProbability := by sorry
