-- Prove2me | Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_sigmaEquiv_mem_stabilizerCode_dual_of_mem_rowCode
-- name    : QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.sigmaEquiv_mem_stabilizerCode_dual_of_mem_rowCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:06:26.310432+00:00
-- url     : https://prove2.me/theorems/88bd8b6c-d513-461c-882e-5c8df825c5cf
-- title:
--   Weighted Triorthogonal Matrix: sigma Equiv mem stabilizer Code dual of mem row Code
-- statement:
--   Every scaled full-row word is orthogonal to the stabilizer span.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/WeightedTriorthogonalCSS.lean#L348-L368
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/WeightedTriorthogonalCSS.lean#L348-L368

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

theorem QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.sigmaEquiv_mem_stabilizerCode_dual_of_mem_rowCode
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    {x : Why24Word Site} (hx : x ∈ R.rowCode.carrier) :
    R.sigmaEquiv x ∈ R.stabilizerCode.dual.carrier := by sorry
