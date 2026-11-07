-- Prove2me | Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_uOneSevenAtAmplitude_eq_why24UOneSeven
-- name    : QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.uOneSevenAtAmplitude_eq_why24UOneSeven
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:08:35.2912+00:00
-- url     : https://prove2.me/theorems/8941f6d2-c78e-41e8-aa29-45bcc0191049
-- title:
--   Weighted Triorthogonal Matrix: u One Seven At Amplitude eq why24 UOne Seven
-- statement:
--   Each local coefficient is exactly the corresponding matrix coefficient of #885's gate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/WeightedTriorthogonalCSS.lean#L1376-L1381
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/WeightedTriorthogonalCSS.lean#L1376-L1381

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Phase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_WeightedTriorthogonalCSS
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Why24WeightedTriorthogonalCSS
open QEC.Coding QEC.Semantics
open scoped BigOperators
open QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
variable {Logical Stabilizer Site : Type}
variable [Fintype Logical] [DecidableEq Logical]
variable [Fintype Stabilizer] [DecidableEq Stabilizer]
variable [Fintype Site] [DecidableEq Site]

theorem QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.uOneSevenAtAmplitude_eq_why24UOneSeven {Index : Type}
    (index : Index) (label : Why24Word Index) :
    uOneSevenAtAmplitude index label =
      why24UOneSeven (why24QuditComputationalBasis (label index)) (label index) := by sorry
