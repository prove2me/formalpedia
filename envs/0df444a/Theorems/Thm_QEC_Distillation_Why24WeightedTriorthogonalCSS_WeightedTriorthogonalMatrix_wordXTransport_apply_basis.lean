-- Prove2me | Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_wordXTransport_apply_basis
-- name    : QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.wordXTransport_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:05:58.389183+00:00
-- url     : https://prove2.me/theorems/13400432-e37e-42e9-a3cd-e4f73496af32
-- title:
--   Weighted Triorthogonal Matrix: word XTransport apply basis
-- statement:
--   Field-X sends a computational ket to the translated ket.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/WeightedTriorthogonalCSS.lean#L865-L882
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/WeightedTriorthogonalCSS.lean#L865-L882

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

theorem QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.wordXTransport_apply_basis {Index : Type}
    [Fintype Index] [DecidableEq Index]
    (word label : Why24Word Index) :
    wordXTransport word (registerBasisKet label) = registerBasisKet (label + word) := by sorry
