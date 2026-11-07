-- Prove2me | Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_logicalZPhysical_intertwines_basis
-- name    : QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.logicalZPhysical_intertwines_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:07:16.803196+00:00
-- url     : https://prove2.me/theorems/a8017811-d2da-41cd-b55f-e251bb53f75b
-- title:
--   Weighted Triorthogonal Matrix: logical ZPhysical intertwines basis
-- statement:
--   Physical and logical Z agree on every encoded computational basis state.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/WeightedTriorthogonalCSS.lean#L1128-L1140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/WeightedTriorthogonalCSS.lean#L1128-L1140

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

theorem QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.logicalZPhysical_intertwines_basis
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (a : Logical) (gamma : F1024) (u : Logical → F1024) :
    R.logicalZPhysical a gamma
        (R.encodedCode.encode (registerBasisKet u)) =
      R.encodedCode.encode (R.logicalZLogical a gamma (registerBasisKet u)) := by sorry
