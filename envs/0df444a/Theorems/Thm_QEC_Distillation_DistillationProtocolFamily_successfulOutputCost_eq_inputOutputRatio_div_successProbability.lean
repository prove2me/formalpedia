-- Prove2me | Theorems.Thm_QEC_Distillation_DistillationProtocolFamily_successfulOutputCost_eq_inputOutputRatio_div_successProbability
-- name    : QEC.Distillation.DistillationProtocolFamily.successfulOutputCost_eq_inputOutputRatio_div_successProbability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:18:17.904944+00:00
-- url     : https://prove2.me/theorems/791c3d3e-68ff-483e-a89c-3051baa6f4a0
-- title:
--   Distillation Protocol Family: successful Output Cost eq input Output Ratio div success Probability
-- statement:
--   Successful-output cost is the direct ratio divided by success probability.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/Overhead.lean#L95-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/Overhead.lean#L95-L101

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

theorem QEC.Distillation.DistillationProtocolFamily.successfulOutputCost_eq_inputOutputRatio_div_successProbability
    (family : DistillationProtocolFamily Resource Input Output Index)
    (index : Index) :
    family.successfulOutputCost index =
      family.inputOutputRatio index /
        (family.protocol index).run.successProbability := by sorry
