-- Prove2me | Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_sigmaEquiv_not_mem_rowCode_dual_of_mem_rowCode_not_mem_stabilizerCode
-- name    : QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.sigmaEquiv_not_mem_rowCode_dual_of_mem_rowCode_not_mem_stabilizerCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:06:26.567863+00:00
-- url     : https://prove2.me/theorems/38ff1b19-7637-410b-a2bf-8f556d69320c
-- title:
--   Weighted Triorthogonal Matrix: sigma Equiv not mem row Code dual of mem row Code not mem stabilizer Code
-- statement:
--   A nontrivial X-sector representative maps to a nontrivial Z-sector representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/WeightedTriorthogonalCSS.lean#L371-L429
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/WeightedTriorthogonalCSS.lean#L371-L429

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

theorem QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.sigmaEquiv_not_mem_rowCode_dual_of_mem_rowCode_not_mem_stabilizerCode
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    {x : Why24Word Site} (hx : x ∈ R.rowCode.carrier)
    (hxOutside : x ∉ R.stabilizerCode.carrier) :
    R.sigmaEquiv x ∉ R.rowCode.dual.carrier := by sorry
