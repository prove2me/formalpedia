-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalDefectStorage_encoder_mul_reference
-- name    : QEC.Coding.BDL26LogicalDefectStorage.encoder_mul_reference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T20:09:51.677656+00:00
-- url     : https://prove2.me/theorems/525b01ab-7d39-43ab-a89b-ceebb98d2883
-- title:
--   BDL26 Logical Defect Storage: encoder mul reference
-- statement:
--   The BDL26 Logical Defect Storage construction uses the encoder mul reference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L199-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDefectStorage.lean#L199-L203

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

theorem QEC.Coding.BDL26LogicalDefectStorage.encoder_mul_reference (beta : ℝ) (eta : DensityOperator Qubit.QubitSpace) :
    encoder S n beta eta.toOperator = observable S n eta * (reference S n beta).toOperator := by sorry
