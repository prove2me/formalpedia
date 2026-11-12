-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_zero_time
-- name    : QEC.Coding.BDL26LogicalDefectStorage.zero_time
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:42:03.060431+00:00
-- url     : https://prove2.me/theorems/f4d6c325-4a83-4164-8801-1296fea1a769
-- title:
--   BDL26 Logical Defect Storage: zero time
-- statement:
--   Time zero does not require positivity, detailed balance or a nonzero mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L556-L567
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L556-L567

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectStorage
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalDefectStorage
open Classical Semantics BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26LogicalDefectStorage._p2m_local_instance_444300d501_96
attribute [local instance] QEC.Coding.BDL26LogicalDefectStorage._p2m_local_instance_444300d501_97

theorem QEC.Coding.BDL26LogicalDefectStorage.zero_time (rate : Rate S n) (beta : ℝ) (eta : DensityOperator Qubit.QubitSpace) :
    encodedError S n rate beta eta 0 (le_refl 0) = 0 ∧
    decodedError S n rate beta eta 0 (le_refl 0) = 0 := by sorry
