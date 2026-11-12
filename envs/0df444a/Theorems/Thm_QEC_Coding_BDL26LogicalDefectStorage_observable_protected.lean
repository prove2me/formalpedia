-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_observable_protected
-- name    : QEC.Coding.BDL26LogicalDefectStorage.observable_protected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T20:22:30.162759+00:00
-- url     : https://prove2.me/theorems/8981d232-04c0-413c-879f-a347fb32c662
-- title:
--   BDL26 Logical Defect Storage: observable protected
-- statement:
--   The BDL26 Logical Defect Storage construction uses the observable protected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L193-L197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L193-L197

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

theorem QEC.Coding.BDL26LogicalDefectStorage.observable_protected (rate : Rate S n) (eta : DensityOperator Qubit.QubitSpace) :
    JumpProtected (jumps S n rate) (observable S n eta) (projector S n) := by sorry
