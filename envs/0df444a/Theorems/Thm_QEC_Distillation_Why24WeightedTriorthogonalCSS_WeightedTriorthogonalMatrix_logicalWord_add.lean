-- Prove2me | Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_logicalWord_add
-- name    : QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.logicalWord_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:06:43.852869+00:00
-- url     : https://prove2.me/theorems/cff80d27-bf7e-4872-9420-0bdd56428ce2
-- title:
--   Weighted Triorthogonal Matrix: logical Word add
-- statement:
--   The logical-row combination is additive.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/WeightedTriorthogonalCSS.lean#L513-L521
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/WeightedTriorthogonalCSS.lean#L513-L521

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

theorem QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.logicalWord_add
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u v : Logical → F1024) :
    R.logicalWord (u + v) = R.logicalWord u + R.logicalWord v := by sorry
