-- Prove2me | Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_rowCode_eq_stabilizerCode_sup_logicalCode
-- name    : QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.rowCode_eq_stabilizerCode_sup_logicalCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:07:46.453773+00:00
-- url     : https://prove2.me/theorems/3113007e-af57-4705-9f07-9099823dbd62
-- title:
--   Weighted Triorthogonal Matrix: row Code eq stabilizer Code sup logical Code
-- statement:
--   The full displayed row span is exactly `G₀ + G₁`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/WeightedTriorthogonalCSS.lean#L273-L292
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/WeightedTriorthogonalCSS.lean#L273-L292

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

theorem QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.rowCode_eq_stabilizerCode_sup_logicalCode
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site) :
    R.rowCode.carrier =
      R.stabilizerCode.carrier ⊔ R.logicalCode.carrier := by sorry
