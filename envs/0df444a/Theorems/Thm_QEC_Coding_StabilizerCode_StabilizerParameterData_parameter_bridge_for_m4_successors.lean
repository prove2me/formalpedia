-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_StabilizerParameterData_parameter_bridge_for_m4_successors
-- name    : QEC.Coding.StabilizerCode.StabilizerParameterData.parameter_bridge_for_m4_successors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:42:49.206404+00:00
-- url     : https://prove2.me/theorems/bc621766-8cb5-4842-b6d1-d9d8ce5bee4c
-- title:
--   Stabilizer Parameter Data: parameter bridge for m4 successors
-- statement:
--   Downstream API for #368, #375, and #384: semantic parameter data supplies the
--   exact rank-derived encoded-qubit count and actual common-fixed carrier
--   dimension, while `generatorSupport` exposes the binary Pauli support of every
--   fixed generator without asserting any successor theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Parameters.lean#L411-L418
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Parameters.lean#L411-L418

import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_Parameters
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
universe u v
open QEC.Coding.StabilizerCode
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode.StabilizerParameterData

theorem QEC.Coding.StabilizerCode.StabilizerParameterData.parameter_bridge_for_m4_successors
    (D : StabilizerParameterData (ι := ι) (κ := κ)) :
    D.blockLength = Fintype.card ι ∧
      D.encodedQubits = D.blockLength - D.presentation.generatorRank ∧
      D.semanticCodeDimension = 2 ^ D.encodedQubits ∧
      SemanticStabilizerDistance D.presentation.code D.distance := by sorry
