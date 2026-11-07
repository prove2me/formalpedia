-- Prove2me | Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_wordPairing_dualLogicalRow_cosetLabel
-- name    : QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.wordPairing_dualLogicalRow_cosetLabel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:07:12.431075+00:00
-- url     : https://prove2.me/theorems/74ddfac6-6554-40d1-b374-038f5b96fa71
-- title:
--   Weighted Triorthogonal Matrix: word Pairing dual Logical Row coset Label
-- statement:
--   The physical Z representative has the expected phase on every coset label.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/WeightedTriorthogonalCSS.lean#L1081-L1093
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/WeightedTriorthogonalCSS.lean#L1081-L1093

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

theorem QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.wordPairing_dualLogicalRow_cosetLabel
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (u : Logical → F1024) (h : R.StabilizerCarrier) (a : Logical) :
    wordPairing (R.dualLogicalRow a) (R.cosetLabel u h) = u a := by sorry
